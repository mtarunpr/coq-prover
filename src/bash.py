"""
To show/test the power of our environment, this provides a "Bashing" solver
which just tries everything until it finds a solution.
"""
from actions.tactics import TACTIC_MAP
from env import Env, pretty_print_proof
from mdp import Action
from typing import Union
from tqdm import tqdm


class Basher:
    """
    A class that takes in an environment, and bashes a solution
    """

    def __init__(self, max_depth: int = 10):
        self.max_depth = max_depth

    def bash(self, initial_env: Env) -> Union[list[str], None]:
        """
        Bash out the solution to the given environment, or give up cuz it's hard
        """
        depth = 0
        to_try = [initial_env]
        solution_state = None
        while depth < self.max_depth and solution_state is None:
            print(f"At depth {depth}, managing {len(to_try)} envs")
            new_to_try = []
            for env in tqdm(to_try):
                for tactic_idx in tqdm(TACTIC_MAP):
                    action = Action(fringe_idx=depth, goal_idx=0, tactic_idx=tactic_idx)
                    (state, reward, done, _) = env.try_step(action)
                    if done:
                        solution_state = state
                        break
                    if reward < 0:
                        continue
                    new_env = env.clone()
                    new_env.step(action)
                    new_to_try.append(new_env)
            to_try = new_to_try
            depth += 1
        if solution_state is None or len(solution_state.fringes) <= 0:
            return None
        return solution_state.fringes[-1].proof


if __name__ == "__main__":
    # Simple example
    env = Env(
        "Lemma one_min_div : forall (n:nat),(divides n 1).",
        [
            "Require Import Wf_nat.",
            "Definition divides (a b:nat) := exists q:nat,a = (b*q).",
        ],
        ["intros.", "red.", "exists n."],
    )
    # Bash it!
    basher = Basher()
    solution = basher.bash(env)
    pretty_print_proof(solution)
