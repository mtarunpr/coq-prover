from alectryon.serapi import annotate
from contextlib import redirect_stderr

TEST_INP = ["Example xyz (H: False): True. (* ... *) exact I. Qed.", "Print xyz."]

# It seems coq errors aren't returned to the var, but bubble up to stderr
# Simplest way to do it is just to catch it there, a little overkill but should be fine
SCRATCH_FILE = "scratch_err.out"


def get_reward_simple(state: list[str], action: str):
    """
    Given a list of previous statements, and the next action (statement)
    return a reward for that pair
    """
    combined = state[:] + [action]
    with open(SCRATCH_FILE, "w") as f:
        with redirect_stderr(f):
            chunks = annotate(combined)
    with open(SCRATCH_FILE, "r") as f:
        if len(f.read()) > 0:
            # Compilation failed, punish our bot
            return -1
    if len(chunks) <= 0:
        # Should never happen
        return -1
    if len(chunks[-1][0].goals) <= 0:
        return 1
    # Simplified return function: No bonus for simplifying state
    return 0


# Returns 1, since after applying "exact I." the goal is solved
get_reward_simple(["Example xyz (H: False): True. "], "exact I.")

# Returns -1, since "improper Action" is malformed
get_reward_simple(["Example xyz (H: False): True. "], "improper Action.")
