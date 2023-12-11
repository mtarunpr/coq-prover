from typing import NamedTuple
from alectryon.core import Hypothesis
import torch
from sentence_transformers import SentenceTransformer
import os

embedding_model = SentenceTransformer("sentence-transformers/all-mpnet-base-v2")
os.environ["TOKENIZERS_PARALLELISM"] = "false"


class Action(NamedTuple):
    fringe_idx: int
    goal_idx: int
    tactic_idx: int


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
            self.embedding = torch.from_numpy(
                embedding_model.encode(goal_to_string(self))
            )
        return self.embedding

    def __str__(self) -> str:
        return self.conclusion


class Fringe(NamedTuple):
    # What sequence of sentences define this fringe
    proof: list[str]
    # What goals (hypotheses included in goal) define this fringe
    goals: list[Goal]


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
