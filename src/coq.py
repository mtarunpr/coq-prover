import random
from strenum import StrEnum
from typing import Union, Optional


class DefinitionKeyword(StrEnum):
    DEFINITION = "Definition"
    FIXPOINT = "Fixpoint"
    COFIXPOINT = "CoFixpoint"
    INDUCTIVE = "Inductive"


class TheoremKeyword(StrEnum):
    THEOREM = "Theorem"
    LEMMA = "Lemma"
    FACT = "Fact"
    REMARK = "Remark"
    COROLLARY = "Corollary"
    PROPOSITION = "Proposition"
    PROPERTY = "Property"
    EXAMPLE = "Example"


class Definition:
    keyword: DefinitionKeyword
    name: str
    args: str
    type: str
    definition: str
    preamble: list[Union["Definition", "Theorem"]]

    def __init__(
        self,
        keyword: DefinitionKeyword,
        name: str,
        args: Optional[str],
        type: Optional[str],
        definition: str,
        preamble: list[str],
    ):
        self.keyword = keyword
        self.name = name
        self.args = args
        self.type = type
        self.definition = definition
        self.preamble = preamble

    def __str__(self):
        return (
            self.keyword
            + " "
            + self.name
            + ((" " + self.args) if self.args else "")
            + ((" : " + self.type) if self.type else "")
            + " := "
            + self.definition
            + "."
        )


class Theorem:
    keyword: TheoremKeyword
    name: str
    statement: str
    proof: list[str]
    preamble: list[Union["Definition", "Theorem"]]

    def __init__(
        self,
        keyword: TheoremKeyword,
        name: str,
        statement: str,
        proof: list[str],
        preamble: list[str],
    ):
        self.keyword = keyword
        self.name = name
        self.statement = statement
        self.proof = proof
        self.preamble = preamble

    def __str__(self):
        return self.keyword + " " + self.name + " : " + self.statement + "."

    def get_random_state(self):
        """
        Get a random intermediate state from within the proof.
        """
        length = random.randint(0, len(self.proof))
        return self.proof[:length]
