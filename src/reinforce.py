import argparse
import torch
import torch.nn as nn
import torch.optim as optim
import torch.nn.functional as F
from torch.autograd import Variable
from mdp import Action
import numpy as np
import os
from data import theorems
from env import Env
from mdp import State
from actions import tactics


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
    help="number of episodes to train for",
)
parser.add_argument(
    "--max-steps",
    type=int,
    default=10000,
    metavar="N",
    help="max number of steps per episode",
)
parser.add_argument(
    "--ckpt-freq",
    type=int,
    default=1000,
    metavar="N",
    help="frequency of saving checkpoints",
)
args = parser.parse_args()


if args.seed:
    torch.manual_seed(args.seed)
    np.random.seed(args.seed)


class GoalNetwork(nn.Module):
    def __init__(self, goal_embedding_dim: int, hidden_size=128):
        super(GoalNetwork, self).__init__()
        self.linear1 = nn.Linear(goal_embedding_dim, hidden_size)
        self.dropout = nn.Dropout(p=0.6)
        self.linear2 = nn.Linear(hidden_size, 1)

    def forward(self, x: torch.Tensor):
        # Given a goal embedding, output logits representing how easy the goal is to prove
        x = self.linear1(x)
        x = self.dropout(x)
        x = F.relu(x)
        action_scores = self.linear2(x)
        return action_scores


class TacticNetwork(nn.Module):
    def __init__(self, goal_embedding_dim: int, num_tactics: int, hidden_size=128):
        super(TacticNetwork, self).__init__()
        self.linear1 = nn.Linear(goal_embedding_dim, hidden_size)
        self.dropout = nn.Dropout(p=0.6)
        self.linear2 = nn.Linear(hidden_size, num_tactics)

    def forward(self, x: torch.Tensor):
        # Given a goal embedding, output a tensor of logits representing how likely each tactic is the best tactic to use next
        x = self.linear1(x)
        x = self.dropout(x)
        x = F.relu(x)
        action_scores = self.linear2(x)
        return action_scores


class Policy(nn.Module):
    def __init__(self, goal_embedding_dim: int, num_tactics: int):
        super(Policy, self).__init__()
        self.fringe_dim = 1
        self.tactic_dim = num_tactics
        self.goal_network = GoalNetwork(goal_embedding_dim)
        self.tactic_network = TacticNetwork(goal_embedding_dim, num_tactics)

    def forward(self, state: State):
        # Given a state, output an action
        # Compute score for each fringe by summing over the scores (logits) of its goals
        fringe_logits = []
        for fringe in state.fringes:
            goal_embeddings = torch.stack(
                map(lambda goal: goal.embedding, fringe.goals)
            )
            goal_logits = self.goal_network(goal_embeddings)
            fringe_logits.append(goal_logits.sum())
        fringe_logits = torch.stack(fringe_logits)
        fringe_probs = F.softmax(fringe_logits)

        # Sample a fringe based on fringe_scores
        fringe_idx = fringe_probs.multinomial(1).data[0]

        # Compute scores for each tactic (based on the 0th goal in the sampled fringe)
        tactic_scores = self.tactic_network(state.fringes[fringe_idx].goals[0])
        tactic_probs = F.softmax(tactic_scores)

        # Sample a tactic based on tactic_scores
        tactic_idx = tactic_probs.multinomial(1).data[0]

        # TODO: fix this; action selection happens in select_action, so just return probs here?

        return (Action(fringe_idx, tactic_idx), fringe_probs, tactic_probs)


class REINFORCE:
    def __init__(self, goal_embedding_dim, num_tactics):
        self.policy = Policy(goal_embedding_dim, num_tactics)
        self.policy = self.policy.cuda()
        self.optimizer = optim.Adam(self.policy.parameters(), lr=args.learning_rate)
        self.policy.train()

    def select_action(self, state: State) -> (Action, torch.Tensor, torch.Tensor):
        probs = self.policy(state)
        action = probs.multinomial().data
        prob = probs[:, action[0, 0]].view(1, -1)
        log_prob = prob.log()
        entropy = -(probs * probs.log()).sum()

        return action[0], log_prob, entropy

    def update_parameters(self, rewards, log_probs, entropies, gamma):
        R = torch.zeros(1, 1)
        loss = 0
        for i in reversed(range(len(rewards))):
            R = gamma * R + rewards[i]
            loss = (
                loss
                - (log_probs[i] * (Variable(R).expand_as(log_probs[i])).cuda()).sum()
                - (0.0001 * entropies[i].cuda()).sum()
            )
        loss = loss / len(rewards)

        self.optimizer.zero_grad()
        loss.backward()
        nn.utils.clip_grad_norm(self.policy.parameters(), 40)
        self.optimizer.step()


def main():
    agent = REINFORCE(256, len(tactics.TACTIC_MAP))

    dir = "ckpt"
    if not os.path.exists(dir):
        os.mkdir(dir)

    for i_episode in range(args.num_episodes):
        theorem, preamble = theorems.get_random_theorem()
        env = Env(theorem, preamble)
        state = env.state
        entropies = []
        log_probs = []
        rewards = []
        for t in range(args.max_steps):
            action, log_prob, entropy = agent.select_action(state)
            action = action.cpu()

            state, reward = env.step(action)
            # We're done if the newest fringe has no goals
            done = len(state.fringes[-1].goals) == 0

            entropies.append(entropy)
            log_probs.append(log_prob)
            rewards.append(reward)

            if done:
                break

        agent.update_parameters(rewards, log_probs, entropies, args.gamma)

        if i_episode % args.ckpt_freq == 0:
            torch.save(
                agent.policy.state_dict(),
                os.path.join(dir, "reinforce-" + str(i_episode) + ".pkl"),
            )

        print("Episode: {}, reward: {}".format(i_episode, np.sum(rewards)))


if __name__ == "__main__":
    main()
