from pathlib import Path
import re
from coq import Theorem, Definition, TheoremKeyword, DefinitionKeyword
from typing import Union

# List of all docs and keys for import
FILES_ORDER = [
    "handcrafted.v",
    # "missing.v",
    # "tactics.v",
    # "division.v",
    # "euclide.v",
    # "permutation.v",
    # "power.v",
    # "gcd.v",
    # "primes.v",
    # "nthroot.v",
]


def parse_file(
    file_name: str,
    path: Path,
) -> list[Union[Theorem, Definition]]:
    """
    Parses a .v file and returns a list of Definitions and Theorems,
    maintaining the order in which they were declared.
    """
    print(f"Parsing {file_name}...")

    defns_and_thms = []

    with open(path / file_name, "r") as file:
        file_contents = file.read()

    # Remove all comments
    file_contents = re.sub(r"\(\*.*?\*\)", "", file_contents, flags=re.DOTALL)

    defn_regex = (
        "("
        + "|".join([type.value for type in DefinitionKeyword])
        + ")"
        + r"\s+([\w']+?)(?:\s+([\w:\(\)]+?))?\s*(?::[^=]\s*(.*?))?\s*:=\s*(.*?)\."
    ) # does not support definitions with proofs

    thm_regex = (
        "("
        + "|".join([type.value for type in TheoremKeyword])
        + ")"
        + r"\s+([\w']+?)\s*:\s*(.*?)\.\s*(?:Proof\.)?\s*(.*?)\s*(?:Qed|Defined)\."
    )

    # Parse all definitions and theorems using regex
    matches = re.findall(
        "(?:" + defn_regex + ")|(?:" + thm_regex + ")",
        file_contents,
        flags=re.DOTALL,
    )

    for match in matches:
        if match[0]:
            keyword, name, args, type, definition_str, _, _, _, _ = match
            assert keyword in [type.value for type in DefinitionKeyword]
            defns_and_thms.append(
                Definition(
                    keyword,
                    name,
                    args if args else None,
                    type if type else None,
                    definition_str,
                    defns_and_thms.copy(),
                )
            )
        else:
            _, _, _, _, _, keyword, name, statement, proof = match
            assert keyword in [type.value for type in TheoremKeyword]
            proof_list = re.findall(r"(.+?\.)\s+", proof, flags=re.DOTALL)
            defns_and_thms.append(
                Theorem(keyword, name, statement, proof_list, defns_and_thms.copy())
            )

    return defns_and_thms


# Iterate over all files to get data
def get_all_theorems(path: Path):
    for file_name in FILES_ORDER:
        defns_and_thms = parse_file(
            file_name,
            path,
        )

    return defns_and_thms


if __name__ == "__main__":
    theorems = get_all_theorems(Path(__file__).parent / "raw")
    print(theorems[-10].name)
    print(theorems[-10].statement)
    print(theorems[-10].preamble)
