import argparse
import torch
import torch.nn as nn
import torch.optim as optim
import torch.nn.functional as F
from mdp import Action
import numpy as np
import os
from data import theorems
from env import Env, pretty_print_proof
from mdp import State
from actions import tactics
from collections import deque
from actions.tactics import TACTIC_MAP
from embedding import embed

parser = argparse.ArgumentParser()
parser.add_argument(
    "--gamma",
    type=float,
    default=0.99,
    metavar="G",
    help="discount factor (default: 0.99)",
)
parser.add_argument("--seed", type=int, default=543, metavar="N", help="random seed")
parser.add_argument(
    "--log-interval",
    type=int,
    default=10,
    metavar="N",
    help="interval between training status logs (default: 10)",
)
parser.add_argument(
    "--learning-rate",
    type=float,
    default=1e-3,
    metavar="LR",
    help="learning rate (default: 1e-3)",
)
parser.add_argument(
    "--num-episodes",
    type=int,
    default=10000,
    metavar="N",
    help="number of episodes to train for (default: 10000)",
)
parser.add_argument(
    "--max-steps",
    type=int,
    default=10000,
    metavar="N",
    help="max number of steps per episode (default: 10000)",
)
parser.add_argument(
    "--ckpt-interval",
    type=int,
    default=1000,
    metavar="N",
    help="interval between checkpoints (default: 1000)",
)
parser.add_argument(
    "--render",
    action="store_true",
    default=False,
    help="render the environment (i.e. print out the attempted proof at each step)",
)
args = parser.parse_args()


if args.seed:
    torch.manual_seed(args.seed)
    np.random.seed(args.seed)


class GoalNetwork(nn.Module):
    def __init__(self, embedding_dim: int, hidden_size=128):
        super(GoalNetwork, self).__init__()
        self.sequential = nn.Sequential(
            nn.Linear(embedding_dim, 2 * hidden_size),
            nn.Dropout(p=0.25),
            nn.ReLU(),
            nn.Linear(2 * hidden_size, hidden_size),
            nn.Dropout(p=0.25),
            nn.ReLU(),
            nn.Linear(hidden_size, 1),
        )

    def forward(self, goal_embedding: torch.Tensor):
        # Given a goal embedding, output logits representing how easy the goal is to prove
        return self.sequential(goal_embedding)


class TacticNetwork(nn.Module):
    def __init__(self, embedding_dim: int, num_tactics: int, hidden_size=128):
        super(TacticNetwork, self).__init__()
        self.sequential = nn.Sequential(
            nn.Linear(embedding_dim, 2 * hidden_size),
            nn.Dropout(p=0.25),
            nn.ReLU(),
            nn.Linear(2 * hidden_size, hidden_size),
            nn.Dropout(p=0.25),
            nn.ReLU(),
            nn.Linear(hidden_size, num_tactics),
        )

    def forward(self, goal_embedding: torch.Tensor):
        # Given a goal embedding, output a tensor of logits representing how likely each tactic is the best tactic to use next
        return self.sequential(goal_embedding)


class ArgumentNetwork(nn.Module):
    def __init__(self, embedding_dim: int, hidden_size=256):
        super(ArgumentNetwork, self).__init__()
        # LSTM takes embedding of all previous arguments (including tactic name) as input
        self.lstm = nn.LSTM(embedding_dim, hidden_size, batch_first=True)
        # Linear layer takes embedding of the current goal, hidden state of the LSTM,
        # and embedding of a potential next argument as input
        self.linear = nn.Linear(2 * embedding_dim + hidden_size, 1)

    def forward(
        self,
        goal_embedding: torch.Tensor,
        prev_args_embeddings: torch.Tensor,
        arg_space_embeddings: torch.Tensor,
    ):
        # Given a goal embedding and previous argument embedding,
        # output a tensor of logits representing how likely each argument is the best argument to use next
        # dimension of goal_embedding is (embedding_dim,)
        # dimension of prev_args_embeddings is (seq_len, embedding_dim)
        # dimension of arg_space_embeddings is (arg_space_size, embedding_dim)
        # seq_len is #previous arguments + 1 (for tactic name)
        # arg_space_size is number of possible arguments (i.e. #hypotheses + #usable_identifiers)
        lstm_out, (hidden_state, _) = self.lstm(prev_args_embeddings)
        # dimension of lstm_out is (seq_len, hidden_size)
        # dimension of hidden_state is (1, hidden_size)
        # dimension of returned value is (arg_space_size,), i.e. one logit/score for each argument
        return self.linear(
            torch.cat(
                (
                    goal_embedding.unsqueeze(0).expand(
                        arg_space_embeddings.shape[0], -1
                    ),
                    arg_space_embeddings,
                    hidden_state.expand(arg_space_embeddings.shape[0], -1),
                ),
                dim=1,
            )
        ).squeeze(1)


class Policy(nn.Module):
    def __init__(self, embedding_dim: int, num_tactics: int):
        super(Policy, self).__init__()
        self.fringe_dim = 1
        self.tactic_dim = num_tactics
        self.goal_network = GoalNetwork(embedding_dim)
        self.tactic_network = TacticNetwork(embedding_dim, num_tactics)
        self.argument_network = ArgumentNetwork(embedding_dim)

        self.log_probs = []
        self.rewards = []

    def forward(self, state: State, usable_identifiers: list[str]):
        # Given a state, output an action
        # Compute score for each fringe by summing over the scores (logits) of its goals

        fringe_logits = []
        for fringe in state.fringes:
            goal_embeddings = torch.stack(
                list(map(lambda goal: goal.get_embedding(), fringe.goals))
            )
            goal_logits = self.goal_network(goal_embeddings)
            fringe_logits.append(goal_logits.sum())

        fringe_logits = torch.stack(fringe_logits)
        fringe_probs = F.softmax(fringe_logits, dim=0)

        # Sample a fringe based on fringe_scores
        fringe_idx = fringe_probs.multinomial(1).data[0]

        # Compute scores for each tactic (based on the 0th goal in the sampled fringe)
        goal_embedding = state.fringes[fringe_idx].goals[0].get_embedding()
        tactic_scores = self.tactic_network(goal_embedding)
        tactic_probs = F.softmax(tactic_scores, dim=0)

        # Sample a tactic based on tactic_scores
        tactic_idx = tactic_probs.multinomial(1).data[0]

        # Compute scores for each possible argument
        arg_space = [
            "".join(hyp.names) for hyp in state.fringes[fringe_idx].goals[0].hypotheses
        ] + usable_identifiers
        argument_indices = []
        argument_probs_list = []
        tactic = TACTIC_MAP[tactic_idx.item()]
        argc = list(tactic.argc_range)[
            -1
        ]  # Generate the max possible number of args; we'll try all prefixes [:n] of them later
        if len(arg_space) > 0:
            prev_args_embeddings = torch.from_numpy(embed(tactic.command)).unsqueeze(0)
            for _ in range(argc):
                argument_logits = self.argument_network(
                    goal_embedding,
                    prev_args_embeddings,
                    torch.stack([torch.from_numpy(embed(arg)) for arg in arg_space]),
                )
                argument_probs = F.softmax(argument_logits, dim=0)
                argument_probs_list.append(argument_probs)

                # Sample an argument based on argument_scores
                argument_indices.append(argument_probs.multinomial(1).data[0])

                # Update prev_args_embeddings
                prev_args_embeddings = torch.cat(
                    (
                        prev_args_embeddings,
                        torch.from_numpy(
                            embed(arg_space[argument_indices[-1]])
                        ).unsqueeze(0),
                    ),
                    dim=0,
                )

        # pi(a | s) = P(fringe_idx, tactic_idx | s)
        #   = pi(fringe_idx | s) * pi(tactic_idx | fringe_idx, s) * prod_i pi(argument_indices[i] | tactic_idx, fringe_idx, s)
        self.log_probs.append(
            fringe_probs[fringe_idx].log()
            + tactic_probs[tactic_idx].log()
            + sum(
                [
                    argument_probs_list[i][argument_indices[i]].log()
                    for i in range(len(argument_indices))
                ]
            )
        )

        return Action(
            fringe_idx.item(),
            0,
            tactic_idx.item(),
            [arg_space[i] for i in argument_indices],
        )


class REINFORCE:
    def __init__(self, embedding_dim, num_tactics):
        self.policy = Policy(embedding_dim, num_tactics)
        self.optimizer = optim.Adam(self.policy.parameters(), lr=args.learning_rate)
        self.policy.train()

    def finish_episode(self):
        R = 0
        policy_loss = []
        returns = deque()
        eps = np.finfo(np.float32).eps.item()
        for r in self.policy.rewards[::-1]:
            R = r + args.gamma * R
            returns.appendleft(R)
        returns = torch.tensor(returns)
        returns = (returns - returns.mean()) / (returns.std(correction=0) + eps)

        for log_prob, R in zip(self.policy.log_probs, returns):
            policy_loss.append((-log_prob * R).unsqueeze(0))

        self.optimizer.zero_grad()
        policy_loss = torch.cat(policy_loss).sum()
        policy_loss.backward()
        self.optimizer.step()

        self.policy.rewards.clear()
        self.policy.log_probs.clear()


def main():
    agent = REINFORCE(768, len(tactics.TACTIC_MAP))

    ckpt_dir = "ckpt"
    if not os.path.exists(ckpt_dir):
        os.mkdir(ckpt_dir)

    running_reward = 0

    for i_episode in range(args.num_episodes):
        ep_reward = 0
        theorem, proof_so_far = theorems.get_random_state()
        if args.render or i_episode % args.log_interval == 0:
            print("EPISODE {}: {}".format(i_episode, theorem.statement))
        env = Env(theorem.statement, theorem.preamble, proof_so_far, theorem.keywords)
        state = env.state
        for h in range(args.max_steps):
            action = agent.policy(state, env.usable_identifiers)
            state, reward, done, error = env.step(action)

            if args.render:
                fringe_idx, _, tactic_idx, tactic_args = action
                print(
                    f"Action (fringe {fringe_idx}, tactic {TACTIC_MAP[tactic_idx].command}, args {tactic_args})"
                )
                print("Proof so far (only last 5 steps):")
                if error:
                    pretty_print_proof(state.fringes[fringe_idx].proof[-5:])
                else:
                    pretty_print_proof(state.fringes[-1].proof[-5:])
                print("Reward:", reward)
                print()

            agent.policy.rewards.append(reward)
            ep_reward += reward

            if done:
                break

        running_reward = 0.05 * ep_reward + (1 - 0.05) * running_reward
        agent.finish_episode()

        if i_episode % args.ckpt_interval == 0:
            torch.save(
                agent.policy.state_dict(),
                os.path.join(ckpt_dir, "reinforce-" + str(i_episode) + ".pkl"),
            )

        if i_episode % args.log_interval == 0:
            print(
                "Episode reward: {:.2f}\tRunning reward: {:.2f}".format(
                    ep_reward, running_reward
                )
            )


if __name__ == "__main__":
    main()
