import random
from enum import StrEnum


class DefinitionType(StrEnum):
    DEFINITION = "Definition"
    FIXPOINT = "Fixpoint"
    COFIXPOINT = "CoFixpoint"
    INDUCTIVE = "Inductive"


class TheoremType(StrEnum):
    THEOREM = "Theorem"
    LEMMA = "Lemma"
    FACT = "Fact"
    REMARK = "Remark"
    COROLLARY = "Corollary"
    PROPOSITION = "Proposition"
    PROPERTY = "Property"
    EXAMPLE = "Example"


class Definition:
    type: DefinitionType
    name: str
    args: str
    definition: str
    preamble: list["Definition" | "Theorem"]

    def __init__(
        self, type: DefinitionType, name: str, definition: str, preamble: list[str]
    ):
        self.type = type
        self.name = name
        self.definition = definition
        self.preamble = preamble

    def __str__(self):
        return (
            self.type
            + " "
            + self.name
            + " "
            + self.args
            + " := "
            + self.definition
            + "."
        )

    # static function to parse a definition from a string
    @staticmethod
    def parse(definition: str, preamble: list[str]):
        """
        Parse a Definition from a string.
        """
        components = definition.split(" ")
        type = components[0]
        name = components[1]
        # get the arguments of the definition
        args = components[2]
        # get the definition itself
        definition = " ".join(components[4:])
        return Definition(type, name, args, definition, preamble)


class Theorem:
    type: TheoremType
    name: str
    statement: str
    partial_proof: list[str]
    preamble: list["Definition" | "Theorem"]

    def __init__(
        self,
        type: TheoremType,
        name: str,
        statement: str,
        partial_proof: list[str],
        preamble: list[str],
    ):
        self.type = type
        self.name = name
        self.statement = statement
        self.partial_proof = partial_proof
        self.preamble = preamble

    def __str__(self):
        return self.type + " " + self.name + " : " + self.statement + "."

    def get_random_state(self):
        """
        Get a random intermediate state from within the proof.
        """
        length = random.randint(0, len(self.partial_proof))
        return self.partial_proof[:length]
