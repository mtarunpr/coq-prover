from alectryon.serapi import annotate
from alectryon.core import Sentence, Goal, Hypothesis
from contextlib import redirect_stderr
from typing import Union
from actions.tactics import TACTIC_MAP, TacticSpec
from itertools import combinations
from mdp import Action, Fringe, State


def apply_coq(proof: list[str]) -> tuple[Fringe, float]:
    """
    Applies alectryon and returns the chunks and reward
    """
    # It seems coq errors aren't returned to the var, but bubble up to stderr
    # Simplest way to do it is just to catch it there, a little overkill but should be fine
    SCRATCH_FILE = "scratch_err.out"
    with open(SCRATCH_FILE, "w") as f:
        with redirect_stderr(f):
            chunks: list[list[Sentence]] = annotate(proof)
    with open(SCRATCH_FILE, "r") as f:
        if len(f.read()) > 0:
            # Compilation failed, punish our bot
            return (Fringe.null_fringe(), -1)
    if len(chunks) <= 0:
        # Should never happen
        return (Fringe.null_fringe(), -1)
    border = chunks[-1][-1]
    fringe = Fringe(proof, border.goals[:])
    reward = 1 if len(fringe.goals) <= 0 else 0
    return (fringe, reward)


class Env:
    """
    Analog to the `env` environments provided by gym and the likes
    """

    def __init__(
        self, statement: str, preamble: list[str] = [], starter_actions: list[str] = []
    ):
        """
        Initializes an environment trying to prove `statement`, where preamble is
        written in proof environment before the statement, and `starter_actions`
        have already been taken to try to prove the statement.

        For example,
        ```
        Env(
            "Lemma one_min_div : forall (n:nat),(divides n 1).",
            [
                "Require Import Wf_nat.",
                "Definition divides (a b:nat) := exists q:nat,a = (b*q).",
            ],
            [
                "intros.",
                "red."
            ]
        )
        ```
        would create an Env trying to prove `one_min_div`, where all the
        necessary libraries have been imported, and the opening steps of
        the proof have already been taken.
        """
        self.opening_book = preamble[:] + [statement] + starter_actions[:]
        (fringe, _) = apply_coq(self.opening_book)
        self.state = State([fringe])

    def try_all_args(self, action: Action) -> str:
        """
        Given a tactic, bashes all possible arguments, returning the command maximizing
        reward
        """
        # Extract the goal we're trying to prove and hypotheses
        tactic = TACTIC_MAP[action.tactic_idx]
        fringe = self.state.fringes[action.fringe_idx]
        target_goal = fringe.goals[action.goal_idx]
        hyps: list[Hypothesis] = target_goal.hypotheses
        hyp_names = ["".join(hyp.names) for hyp in hyps]
        # Generate all the next sentences to test
        test_blocks: list[str] = []
        for argc in tactic.argc_range:
            for combo in combinations(hyp_names, argc):
                added_block = f"{action.goal_idx + 1}: " + "{\n  " + tactic.command
                for arg_ix in range(argc):
                    added_block += " " + combo[arg_ix]
                added_block += ".\n}"
                test_blocks.append(added_block)
        # Test them, remembering the next line leading to the max reward
        max_command = ""
        max_reward = float("-inf")
        for block in test_blocks:
            new_proof = fringe.proof[:] + [block]
            _, reward = apply_coq(new_proof)
            if reward > max_reward:
                max_reward = reward
                max_command = block
        return max_command

    def step(self, action: Action) -> tuple[State, float]:
        """
        Steps forward in the environment by applying a tactic to a specific fringe.
        Returns the new state and the reward.
        """
        command_with_args = self.try_all_args(action)
        fringe = self.state.fringes[action.fringe_idx]
        new_proof = fringe.proof[:] + [command_with_args]
        (new_fringe, reward) = apply_coq(new_proof)
        self.state.fringes.append(new_fringe)
        return (self.state, reward)

    def try_step(self, action: Action) -> tuple[State, float]:
        """
        Returns what the new state and reward would be after taking the given action,
        without actually changing the environment at all
        """
        command_with_args = self.try_all_args(action)
        fringe = self.state.fringes[action.fringe_idx]
        new_proof = fringe.proof[:] + [command_with_args]
        (new_fringe, reward) = apply_coq(new_proof)
        new_state = State(self.state.fringes[:] + [new_fringe])
        return (new_state, reward)

    def clone(self) -> "Env":
        """
        Copies this environment into a new environment, no mutability concerns
        """
        new_env = Env("", [], [])
        new_env.opening_book = self.opening_book[:]
        new_env.state = State(
            [Fringe(f.proof[:], f.goals[:]) for f in self.state.fringes]
        )
        return new_env


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
    # Apply the "auto." action
    action = Action(0, 0, 11)
    state, reward = env.step(action)
    print(state, reward)
