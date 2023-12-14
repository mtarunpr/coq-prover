from alectryon.serapi import annotate
from alectryon.core import Sentence, Hypothesis
from contextlib import redirect_stderr
from actions.tactics import TACTIC_MAP, tactic_to_idx
from itertools import combinations
from mdp import Action, Fringe, State, Goal
from typing import Optional


def apply_coq(
    proof: list[str], fringes: Optional[list[Fringe]] = None
) -> tuple[Optional[Fringe], float]:
    """
    Applies alectryon and returns the chunks and reward. If fringes is provided,
    penalizes the reward if the fringe already exists.
    """
    # It seems coq errors aren't returned to the var, but bubble up to stderr
    # Simplest way to do it is just to catch it there, a little overkill but should be fine
    SCRATCH_FILE = "scratch_err.out"
    with open(SCRATCH_FILE, "w") as f:
        with redirect_stderr(f):
            chunks: list[list[Sentence]] = annotate(proof)
    with open(SCRATCH_FILE, "r") as f:
        if len(f.read()) > 0:
            # Compilation failed, punish our bot
            return (None, -0.02)
    if len(chunks) == 0:
        # Should never happen
        return (None, -1)
    border = chunks[-1][-1]
    # TODO: minor, but it may be possible for the last chunk to be a Text instead of a Sentence,
    # so we should prob extract the last Sentence
    fringe = Fringe(
        proof,
        [
            Goal(border.goals[i].conclusion, border.goals[i].hypotheses)
            for i in range(len(border.goals))
        ],
    )
    # Penalize if the fringe already exists
    if fringes is not None and fringe in fringes:
        return (None, -0.02)
    # Reward if the fringe is new or (even more) if the theorem has been proven
    reward = 1 if len(fringe.goals) == 0 else 0.1
    return (fringe, reward)


def pretty_print_proof(proof: list[str]) -> str:
    """
    Given a proof (list of strings, one per sentence), pretty prints it
    """
    for sentence in proof:
        print(sentence)


class Env:
    """
    Analog to the `env` environments provided by gym and the likes
    """

    def __init__(
        self,
        statement: str,
        preamble: list[str] = [],
        starter_actions: list[str] = [],
        usable_identifiers: list[str] = [],
    ):
        """
        Initializes an environment trying to prove `statement`, where preamble is
        written in proof environment before the statement, `starter_actions`
        have already been taken to try to prove the statement, and `usable_identifiers`
        are the identifiers (theorems, definitions, etc.) that can be used as tactic arguments
        in the proof.

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
            ],
            []
        )
        ```
        would create an Env trying to prove `one_min_div`, where all the
        necessary libraries have been imported, and the opening steps of
        the proof have already been taken.
        """
        self.opening_book = preamble[:] + [statement] + starter_actions[:]
        (fringe, _) = apply_coq(self.opening_book)
        if fringe is None:
            raise Exception("Invalid opening book. See scratch_err.out for details.")
        self.state = State([fringe])
        self.usable_identifiers = usable_identifiers[:]

    def try_all_args(self, action: Action) -> str:
        """
        Given a tactic, bashes all possible arguments, returning the command maximizing
        reward
        """
        # Extract the goal we're trying to prove and hypotheses
        tactic = TACTIC_MAP[action.tactic_idx]
        fringe = self.state.fringes[action.fringe_idx]
        target_goal = fringe.goals[action.goal_idx]
        hyps: list[Hypothesis] = target_goal.hypotheses
        arg_space = ["".join(hyp.names) for hyp in hyps] + self.usable_identifiers
        # Generate all the next sentences to test
        test_blocks: list[str] = []
        for argc in tactic.argc_range:
            for combo in combinations(arg_space, argc):
                added_block = f"{action.goal_idx + 1}: " + "{\n  " + tactic.command
                for arg_ix in range(argc):
                    added_block += " " + combo[arg_ix]
                added_block += ".\n}"
                test_blocks.append(added_block)
        # Test them, remembering the next line leading to the max reward
        max_command = ""
        max_reward = float("-inf")
        for block in test_blocks:
            new_proof = fringe.proof[:] + [block]
            _, reward = apply_coq(new_proof)
            if reward > max_reward:
                max_reward = reward
                max_command = block
        return max_command

    def step(self, action: Action) -> tuple[State, float, bool, bool]:
        """
        Steps forward in the environment by applying a tactic to a specific fringe.
        Returns the new state, the reward, a boolean representing whether the
        theorem has been proven, and a boolean representing whether the action
        resulted in an error.
        """
        fringe = self.state.fringes[action.fringe_idx]
        tactic = TACTIC_MAP[action.tactic_idx]
        new_proof = fringe.proof[:] + [tactic.command + " ".join(action.arg_list) + "."]
        (new_fringe, reward) = apply_coq(new_proof, self.state.fringes)
        if new_fringe is not None:
            self.state.fringes.append(new_fringe)
            done = len(new_fringe.goals) == 0
        else:
            done = False
        return (self.state, reward, done, new_fringe is None)

    def try_step(self, action: Action) -> tuple[State, float, bool, bool]:
        """
        Returns what the new state and reward would be after taking the given action,
        and whether the theorem will have been proven and whether the action will result in an error,
        without actually changing the environment at all.
        """
        fringe = self.state.fringes[action.fringe_idx]
        tactic = TACTIC_MAP[action.tactic_idx]
        new_proof = fringe.proof[:] + [tactic.command + " ".join(action.arg_list) + "."]
        (new_fringe, reward) = apply_coq(new_proof, self.state.fringes)
        new_state = (
            State(self.state.fringes[:] + [new_fringe])
            if new_fringe is not None
            else self.state
        )
        done = len(new_fringe.goals) == 0 if new_fringe is not None else False
        return (new_state, reward, done, new_fringe is None)

    def clone(self) -> "Env":
        """
        Copies this environment into a new environment, no mutability concerns
        """
        new_env = Env("", [], [], [])
        new_env.opening_book = self.opening_book[:]
        new_env.state = State(
            [Fringe(f.proof[:], f.goals[:]) for f in self.state.fringes]
        )
        return new_env


if __name__ == "__main__":
    # Simple example
    env = Env(
        "Theorem excluded_middle_irrefutable: forall (P : Prop), ~ ~ (P \/ ~ P).",
        [],
        # ["intros.", "red.", "exists n."],
    )
    # Apply the "auto." action
    action = Action(0, 0, tactic_to_idx("intros"))
    state, reward, _, _ = env.step(action)
    print(f"Reward: {reward}")
    print()

    for i, fringe in enumerate(state.fringes):
        print(f"FRINGE {i}")
        pretty_print_proof(fringe.proof)
        print()
        print("Goals:")
        for goal in fringe.goals:
            print(goal)
        print()
