from reinforce import Policy
import argparse
from actions.tactics import TACTIC_MAP
import torch
from env import Env, pretty_print_proof
from data import theorems

parser = argparse.ArgumentParser()
parser.add_argument("--model", type=str, required=True, help="path to model (pkl file)")
parser.add_argument(
    "--max-steps",
    type=int,
    default=10000,
    metavar="N",
    help="max number of steps per episode (default: 10000)",
)
parser.add_argument(
    "--render",
    action="store_true",
    default=False,
    help="render the environment (i.e. print out the attempted proof at each step)",
)
args = parser.parse_args()

policy = Policy(768, len(TACTIC_MAP))
policy.load_state_dict(torch.load(args.model))
policy.eval()

theorem, proof_so_far = theorems.get_random_state()
env = Env(theorem.statement, theorem.preamble, proof_so_far, theorem.keywords)
print(theorem.statement)
print('len of proof so far', len(proof_so_far))
print()
print('AGENT')
state = env.state

ep_reward = 0
for h in range(args.max_steps):
    action = policy(state, env.usable_identifiers, theorem.keyword_to_statement)
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

    policy.rewards.append(reward)
    ep_reward += reward

    if done:
        break
