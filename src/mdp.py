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
    The entire state we have access to at any point. Consists of set of fringes,
    which are like intermediate proof states we've been to before and may backtrack to
    """

    fringes: list[Fringe]
