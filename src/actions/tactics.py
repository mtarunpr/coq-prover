import sys

sys.path.append("..")

from typing import NamedTuple
from actions.data import raw_tactics


class TacticSpec(NamedTuple):
    idx: int
    argc_range: range
    command: str


TACTIC_MAP = {
    idx: TacticSpec(
        idx,
        argc_range,
        command,
    )
    for (idx, (command, argc_range)) in enumerate(raw_tactics)
}


def tactic_to_idx(tactic: str) -> int:
    """
    Given a tactic, return its index in the TACTIC_MAP
    """
    for idx, spec in TACTIC_MAP.items():
        if spec.command == tactic:
            return idx
    return -1
