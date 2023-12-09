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
        range(0, 2),
        command,
    )
    for (idx, command) in raw_tactics
}
