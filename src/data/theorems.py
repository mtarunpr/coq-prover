import random

# (theorem, preamble)
theorems: tuple[str, list[str]] = [
    ('Theorem simple_sum1 : 1 + 1 = 2.', []),
    ('Theorem simple_sum2 : forall (n : nat), n + 0 = n.', []),
    ('Theorem simple_and1 : True /\ True.', []),
    ('Theorem simple_and2 : forall (P Q : Prop), P /\ Q -> Q /\ P.', []),
]

def get_random_theorem():
    return random.choice(theorems)