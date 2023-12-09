from alectryon.serapi import annotate
from contextlib import redirect_stderr


# It seems coq errors aren't returned to the var, but bubble up to stderr
# Simplest way to do it is just to catch it there, a little overkill but should be fine
SCRATCH_FILE = "scratch_err.out"


def get_reward_simple(state: list[str], action: str):
    """
    Given a list of previous statements, and the next action (statement)
    return a reward for that pair
    """
    combined = state[:] + [action]
    with open(SCRATCH_FILE, "w") as f:
        with redirect_stderr(f):
            chunks = annotate(combined)
    with open(SCRATCH_FILE, "r") as f:
        if len(f.read()) > 0:
            # Compilation failed, punish our bot
            return -1
    if len(chunks) <= 0:
        # Should never happen
        return -1
    print(chunks)
    print(chunks[-1])
    if len(chunks[-1][0].goals) <= 0:
        return 1
    # Simplified return function: No bonus for simplifying state
    return 0


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

    @property
    def list_rep(self):
        """
        Returns the environment as a list of statements which can be
        fed into alectryon.
        """
        return (
            self.preamble + [self.statement] + self.starter_actions + self.taken_actions
        )

    def test(self):
        print(get_reward_simple(self.list_rep, "auto with arith."))


env = Env(
    "Lemma one_min_div : forall (n:nat),(divides n 1).",
    [
        "Require Import Wf_nat.",
        "Definition divides (a b:nat) := exists q:nat,a = (b*q).",
    ],
    ["intros.", "red.", "exists n."],
)

env.test()
