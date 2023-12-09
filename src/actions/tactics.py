from typing import NamedTuple
from data import raw_tactics


class TacticSpec(NamedTuple):
    idx: int
    arg_count_range: range
    command: str


TACTIC_MAP = {
    idx: TacticSpec(
        idx,
        range(0, 3),
        command,
    )
    for (idx, command) in raw_tactics
}

print(TACTIC_MAP)
