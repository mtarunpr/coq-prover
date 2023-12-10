from typing import NamedTuple
from alectryon.core import Sentence, Goal, Hypothesis


class Action(NamedTuple):
    fringe_idx: int
    goal_idx: int
    tactic_idx: int


class Fringe(NamedTuple):
    # What sequence of sentences define this fringe
    proof: list[str]
    # What goals (hypotheses included in goal) define this fringe
    goals: list[Goal]

    @staticmethod
    def null_fringe() -> "Fringe":
        return Fringe([], [])


class State(NamedTuple):
    """
    The entire state we have access to at any point.

    NOTE: You might wonder, where are hypotheses (i.e. named variables) stored?
    These exist within the `Goal` struct, and thus each fringe has multiple sets
    of variables they can apply with tactics. Better to avoid not duplicating this data.
    """

    fringes: list[Fringe]
