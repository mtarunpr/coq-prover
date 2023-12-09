from alectryon.serapi import annotate
from contextlib import redirect_stderr
from typing import Union
from actions.tactics import TACTIC_MAP, TacticSpec
from itertools import combinations

# It seems coq errors aren't returned to the var, but bubble up to stderr
# Simplest way to do it is just to catch it there, a little overkill but should be fine
SCRATCH_FILE = "scratch_err.out"


def apply_coq(proof: list[str]) -> tuple[list["alectryon.Sentence"], float]:
    """
    Applies alectryon and returns the chunks and reward
    """
    with open(SCRATCH_FILE, "w") as f:
        with redirect_stderr(f):
            chunks = annotate(proof)
        with open(SCRATCH_FILE, "r") as f:
            if len(f.read()) > 0:
                # Compilation failed, punish our bot
                return ([], -1)
        if len(chunks) <= 0:
            # Should never happen
            return ([], -1)
        if len(chunks[-1][0].goals) <= 0:
            return (chunks, 1)
        # Simplified return function: No bonus for simplifying state
        return (chunks, 0)


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
        self.statement = statement
        self.preamble = preamble
        self.starter_actions = starter_actions
        self.taken_actions: list[str] = []
        self.last_eval: list[alectryon.Sentence] = []
        starter_proof = self.list_rep
        (chunks, _) = apply_coq(starter_proof)
        self.last_eval = chunks

    @property
    def list_rep(self):
        """
        Returns the environment as a list of statements which can be
        fed into alectryon.
        """
        return (
            self.preamble[:]
            + [self.statement]
            + self.starter_actions[:]
            + self.taken_actions[:]
        )

    def try_all_args(self, fringe_idx: int, tactic: TacticSpec) -> str:
        """
        Given a tactic, bashes all possible arguments, returning the command maximizing
        reward
        """
        # Get all the argument names we care about
        target_goal = self.last_eval[-1][0].goals[fringe_idx]
        hyps: list[alectryon.Hypothesis] = target_goal.hypotheses
        hyp_names = ["".join(hyp.names) for hyp in hyps]
        test_blocks: list[str] = []
        # Generate all the next sentences to test
        for argc in tactic.argc_range:
            for combo in combinations(hyp_names, argc):
                added_block = f"{fringe_idx}: " + "{\n  " + tactic.command
                for arg_ix in range(argc):
                    added_block += " " + combo[arg_ix]
                added_block += ".\n}"
                test_blocks.append(added_block)
        # Test them, remembering the next line leading to the max reward
        max_command = ""
        max_reward = float("-inf")
        for block in test_blocks:
            new_proof = self.list_rep + [block]
            _, reward = apply_coq(new_proof)
            if reward > max_reward:
                max_reward = reward
                max_command = block
        return max_command

    def make_step(self, proof: list[str]):
        """
        Sets the state of the environment to whatever results from applying `proof`
        """

    def step(self, fringe_idx: int, tactic_idx: int) -> (list[str], float):
        """
        Steps forward in the environment by applying a tactic to a specific fringe.
        Returns the list of remaining goals and the reward.
        """
        tactic = TACTIC_MAP[tactic_idx]
        command = self.try_all_args(fringe_idx, tactic)
        print(command)


env = Env(
    "Lemma one_min_div : forall (n:nat),(divides n 1).",
    [
        "Require Import Wf_nat.",
        "Definition divides (a b:nat) := exists q:nat,a = (b*q).",
    ],
    ["intros.", "red.", "exists n."],
)

env.step(0, 44)
