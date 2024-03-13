import random
from strenum import StrEnum
from typing import Union, Optional
from alectryon.serapi import annotate
from contextlib import redirect_stderr
import re

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
        preamble: list[Union["Definition", "Theorem"]], # list of definitions and theorems in all imported files as well as the current file, up to the point of this theorem
        context_str: str, # the contents of the file up to just before the point of this theorem
    ):
        self.keyword = keyword
        self.name = name
        self.statement = statement
        self.proof = proof
        self.preamble = preamble
        self.context_str = context_str

    def __str__(self):
        return self.keyword + " " + self.name + " : " + self.statement + "."
    
    def get_preamble_string(self):
        """
        Get a string representation of the preamble.
        """
        return "\n".join([str(item) for item in self.preamble])
        
    def get_proof_string(self):
        """
        Get a string representation of the proof.
        """
        return "\n".join(self.proof)


    def get_random_state(self):
        """
        Get a random intermediate state from within the proof.
        """
        length = random.randint(0, len(self.proof))
        return self.proof[:length]

def reward_multi(lst):
    return [reward(item) for item in lst]

def reward(file_with_proof: str):
    ERROR_FILE = "coq_logs.err"
    with open(ERROR_FILE, "w") as f:
        with redirect_stderr(f):
            chunks = annotate([file_with_proof])
    with open(ERROR_FILE, "r") as f:
        if len(f.read()) > 0:
            return 0
        else:
            return 1

def parse_proof_from_response(response):
    match = re.search(r"Proof\.(.*?(?:Qed|Defined)\.)", response, re.DOTALL)
    # if match is None:
    #     match = re.search(r"Proof(.*?(?:Qed|Defined)\.)", response, re.DOTALL) # here the proof is the "#### Proof" header
    if match is None:
        return ""
    return match.group(0)