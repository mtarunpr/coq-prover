import random
from .parser import get_all_theorems
from pathlib import Path
from .coq import Theorem


# (theorem, preamble)
theorems: list[Theorem] = [
    Theorem(
        "simple_sum1",
        "Theorem simple_sum1: 1 + 1 = 2.",
        ["reflexivity."],
        [],
        [],
    ),
    Theorem(
        "simple_sum2",
        "Theorem simple_sum2: forall (n : nat), n + 0 = n.",
        ["induction n.", "simpl.", "rewrite IHn.", "reflexivity."],
        [],
        [],
    ),
    Theorem(
        "simple_and1",
        "Theorem simple_and1 : forall (P Q : Prop), P /\ Q -> Q /\ P.",
        ["intros P Q H.", "destruct H.", "split.", "exact H0.", "exact H."],
        [],
        [],
    ),
]

theorems += get_all_theorems(Path(__file__).parent / "raw")


def get_random_state():
    theorem = random.choice(theorems)
    return theorem.statement, theorem.preamble, theorem.get_random_state()
