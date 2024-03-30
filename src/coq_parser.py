from pathlib import Path
import re
from coq import Theorem, Definition, TheoremKeyword, DefinitionKeyword
from typing import Union
import os
import csv
import argparse


ADD_IMPORTED_DECLARATIONS = True


def parse_file(
    file_name: str,
    path: Path,
) -> tuple[list[str], list[Union[Theorem, Definition]]]:
    """
    Parses a .v file and returns a list of import strings as well as a list of
    Definitions and Theorems, maintaining the order in which they were declared.
    """
    print(f"Parsing {file_name}...")

    defns_and_thms = []

    with open(path / file_name, "r") as file:
        file_contents = file.read()

    # Remove all comments (supports 3 levels of nested comments)
    file_contents = re.sub(
        r"\(\*(?:(?!\(\*|\*\)).|(?:\(\*(?:(?!\(\*|\*\)).|(?:\(\*(?:(?!\(\*|\*\)).)*\*\)))*\*\)))*\*\)",
        "",
        file_contents,
        flags=re.DOTALL,
    )

    # Parse imports
    imports = re.findall(r"(?:Require\s+)?(?:Im|Ex)port\s+(.+?)\.\s", file_contents)

    # Parse all definitions and theorems
    defn_regex = (
        "("
        + "|".join([type.value for type in DefinitionKeyword])
        + ")"
        + r"\s+([\w']+?)(?:\s+([\w:\(\)]+?))?\s*(?::[^=]\s*(.*?))?\s*:=\s*(.*?)\."
    )  # does not support definitions with proofs

    thm_regex = (
        "("
        + "|".join([type.value for type in TheoremKeyword])
        + ")"
        + r"\s+([\w']+?)\s*:[^=]\s*(.*?)\.\s*(?:Proof\.)?\s*(.*?)\s*(?:Qed|Defined)\."
    )

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
            context_str = re.search(
                r"(.+?)" + keyword + r"\s+" + name, file_contents, flags=re.DOTALL
            ).group(1)
            defns_and_thms.append(
                Theorem(
                    keyword,
                    name,
                    statement,
                    proof_list,
                    defns_and_thms.copy(),
                    context_str,
                )
            )

    return imports, defns_and_thms


def parse_all_files(
    path: Path,
) -> dict[str, tuple[list[str], list[Union[Theorem, Definition]]]]:
    """
    Parses all .v files in the given directory and returns a map from file name
    to a tuple of imports and definitions/theorems.
    """

    coq_file_names = []
    for root, _, file_names in os.walk(path):
        if "proofs" in root:
            continue
        for file_name in file_names:
            if file_name.endswith(".v"):
                coq_file_names.append(file_name)

    file_name_to_parsed = {}
    for file_name in coq_file_names:
        imports, defns_and_thms = parse_file(
            file_name,
            path,
        )
        file_name_to_parsed[file_name] = (imports, defns_and_thms)

    # Add definitions and theorems from imported files to the preamble
    # if the imported file is also from the same project
    if ADD_IMPORTED_DECLARATIONS:
        for file_name in coq_file_names:
            imports, defns_and_thms = file_name_to_parsed[file_name]
            for import_name in reversed(imports):
                if f"{import_name}.v" in coq_file_names:
                    for defn_or_thm in defns_and_thms:
                        defn_or_thm.preamble = (
                            file_name_to_parsed[f"{import_name}.v"][1]
                            + defn_or_thm.preamble
                        )

    return file_name_to_parsed


def generate_dataset(project_dir_path: Path, output_file_path: Path):
    """
    Generates a dataset from the given Coq project directory.
    """
    file_name_to_parsed = parse_all_files(project_dir_path)

    # Generate dataset
    dataset = []
    for file_name, (_, defns_and_thms) in file_name_to_parsed.items():
        for defn_or_thm in defns_and_thms:
            if isinstance(defn_or_thm, Definition):
                continue
            preamble_str = "\n".join(
                map(lambda d_or_t: str(d_or_t), defn_or_thm.preamble)
            )
            theorem_str = str(defn_or_thm)
            proof_str = "\n".join(defn_or_thm.proof)
            dataset.append(
                {
                    "file_name": file_name,
                    "preamble": preamble_str,
                    "theorem": theorem_str,
                    "proof": proof_str,
                }
            )

    # Write dataset to file
    output_file_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_file_path, "w") as file:
        writer = csv.DictWriter(file, fieldnames=dataset[0].keys())
        writer.writeheader()
        writer.writerows(dataset)


if __name__ == "__main__":
    # Get a command line argument for the project name
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--project-name",
        required=True,
        help="The name of the Coq project (must be in the raw directory).",
    )
    args = parser.parse_args()

    generate_dataset(
        Path(__file__).parent.parent / "data" / "raw" / args.project_name,
        Path(__file__).parent.parent / "data" / "datasets" / f"{args.project_name}.csv",
    )
