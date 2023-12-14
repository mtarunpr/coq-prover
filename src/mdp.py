from typing import NamedTuple
from alectryon.core import Hypothesis
import torch
from embedding import embed


class Action(NamedTuple):
    fringe_idx: int
    goal_idx: int
    tactic_idx: int
    arg_list: list[str] = []


class Goal:
    conclusion: str
    hypotheses: list[Hypothesis]
    embedding: torch.Tensor

    def __init__(self, conclusion: str, hypotheses: list[Hypothesis]):
        self.conclusion = conclusion
        self.hypotheses = hypotheses
        self.embedding = None

    def get_embedding(self):
        if self.embedding is None:
            self.embedding = embed(goal_to_string(self))
        return self.embedding

    def __str__(self) -> str:
        return self.conclusion

    def __eq__(self, __value: object) -> bool:
        if not isinstance(__value, Goal):
            return False
        if len(self.hypotheses) != len(__value.hypotheses):
            return False
        return (
            all(
                [
                    self.hypotheses[i].names == __value.hypotheses[i].names
                    and self.hypotheses[i].type == __value.hypotheses[i].type
                    for i in range(len(self.hypotheses))
                ]
            )
            and self.conclusion == __value.conclusion
        )


class Fringe(NamedTuple):
    # What sequence of sentences define this fringe
    proof: list[str]
    # What goals (hypotheses included in goal) define this fringe
    goals: list[Goal]

    def __eq__(self, __value: object) -> bool:
        if not isinstance(__value, Fringe):
            return False
        if len(self.goals) != len(__value.goals):
            return False

        return self.goals == __value.goals


class State(NamedTuple):
    """
    The entire state we have access to at any point. Consists of set of fringes,
    which are like intermediate proof states we've been to before and may backtrack to
    """

    fringes: list[Fringe]

    def __str__(self) -> str:
        return "\n".join(
            [
                "Fringe "
                + str(i)
                + ": "
                + (str(fringe.goals[0]) if len(fringe.goals) > 0 else "No goals")
                for (i, fringe) in enumerate(self.fringes)
            ]
        )


def goal_to_string(goal: Goal) -> str:
    """
    Converts a Goal to a string with all hypotheses as well as conclusion
    """

    goal_string = ""
    for hypothesis in goal.hypotheses:
        goal_string += ", ".join(hypothesis.names) + " : " + hypothesis.type + "\n"
    goal_string += "------------------\n"
    goal_string += goal.conclusion
    return goal_string
