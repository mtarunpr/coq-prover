import os
from toposort import toposort_flatten
import argparse


def is_identifier_char(char):
    """
    Returns True if the given character is a valid Coq identifier character.
    """
    return char.isalpha() or char.isdigit() or char == "_" or char == "'"


def get_imports(filename):
    with open(filename, "r") as f:
        lines = f.readlines()
    imports = []
    for line in lines:
        if line.startswith("Require Import"):
            imports.append(line.split("Require Import ")[1].split(".")[0])
        if line.startswith("Require Export"):
            imports.append(line.split("Require Export ")[1].split(".")[0])
        elif line.startswith("From"):
            imports.append(line.split("From ")[1].split(" ")[0])
    return imports


def get_file_dependency_graph(coq_project_path):
    """
    Returns a dictionary mapping each file in the given Coq project to a list
    of files that it imports.
    """
    # Get all .v files in project
    coq_filenames = []
    for root, _, filenames in os.walk(coq_project_path):
        for filename in filenames:
            if filename.endswith(".v"):
                coq_filenames.append(os.path.join(root, filename))

    # Get all imports from each file
    file_imports = {}
    for filename in coq_filenames:
        file_imports[filename] = get_imports(filename)

    # Build dependency graph
    dependency_graph = {}
    for filename in coq_filenames:
        dependency_graph[filename] = []
        for import_ in file_imports[filename]:
            for filename2 in coq_filenames:
                if import_ + ".v" in filename2:
                    dependency_graph[filename].append(filename2)
                    break

    return dependency_graph


def get_ordered_files(coq_project_path):
    """
    Returns a topologically sorted list of files in the given Coq project.
    """
    dependency_graph = get_file_dependency_graph(coq_project_path)
    return toposort_flatten(dependency_graph)


def get_theorem_dependency_graph(coq_project_path):
    """
    Returns a dictionary mapping each theorem or lemma in the given Coq project to a list
    of theorems or lemmas from the same project that it depends on.
    """

    # Get all .v files in project
    coq_filenames = []
    for root, _, filenames in os.walk(coq_project_path):
        for filename in filenames:
            if filename.endswith(".v"):
                coq_filenames.append(os.path.join(root, filename))

    # For each file, get all theorems and lemmas
    file_theorems = {}
    for filename in coq_filenames:
        with open(filename, "r") as f:
            lines = f.readlines()
        theorem_names = []
        for line in lines:
            if line.startswith("Theorem") or line.startswith("Lemma"):
                theorem_names.append(line.split(" ")[1].split(":")[0])
        file_theorems[filename] = theorem_names

    all_project_theorems = [
        theorem for filename in coq_filenames for theorem in file_theorems[filename]
    ]

    # For each theorem or lemma, get all theorems and lemmas that it depends on
    theorem_dependency_graph = (
        {}
    )  # maps theorem/lemma to list of theorems/lemmas that its proof uses
    for filename in coq_filenames:
        # Open file and get all theorems/lemmas that are used in the proof of this theorem/lemma
        with open(filename, "r") as f:
            lines = f.readlines()
        for line in lines:
            if line.startswith("Theorem") or line.startswith("Lemma"):
                theorem_name = line.split(" ")[1].split(":")[0]
                proof = ""
                line_index = lines.index(line)
                for line2 in lines[line_index + 1 :]:
                    proof += line2
                    if "Qed." in line2 or "Defined." in line2:
                        break
                # Get all theorems/lemmas that are used in the proof of this theorem/lemma
                theorem_dependency_graph[theorem_name] = []
                for theorem_name2 in all_project_theorems:
                    # Make sure we don't mistakenly add a theorem that's a substring of another theorem
                    # We can do this by checking that the theorem is surrounded by a non-identifier character
                    if theorem_name2 in proof:
                        theorem_index = proof.index(theorem_name2)
                        if theorem_index == 0 or not is_identifier_char(
                            proof[theorem_index - 1]
                        ):
                            if theorem_index + len(theorem_name2) == len(
                                proof
                            ) or not is_identifier_char(
                                proof[theorem_index + len(theorem_name2)]
                            ):
                                theorem_dependency_graph[theorem_name].append(
                                    theorem_name2
                                )

    return theorem_dependency_graph, file_theorems


def get_ordered_theorems(coq_project_path):
    """
    Returns a topologically sorted list of theorems and lemmas in the given Coq project.
    """
    theorem_dependency_graph, file_theorems = get_theorem_dependency_graph(
        coq_project_path
    )
    toposorted_theorems = toposort_flatten(theorem_dependency_graph)
    # Create pairs of theorems and their file names
    theorem_file_pairs = []
    for theorem in toposorted_theorems:
        for filename in file_theorems:
            if theorem in file_theorems[filename]:
                theorem_file_pairs.append(
                    (theorem, filename.split("/")[-1].split(".")[0])
                )
                break
    return theorem_file_pairs


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "-p",
        "--path",
        help="path to Coq project whose dependency graph to generate",
        required=True,
        type=str,
    )
    parser.add_argument(
        "-f",
        "--files",
        help="generate file dependency graph instead of theorem dependency graph",
        required=False,
        action="store_true",
        default=False,
    )
    args = parser.parse_args()

    if args.files:
        print("File dependency graph", get_file_dependency_graph(args.path))
        print()
        print("Topologically sorted files", get_ordered_files(args.path))
    else:
        print("Theorem dependency graph", get_theorem_dependency_graph(args.path))
        print()
        print("Topologically sorted theorems", get_ordered_theorems(args.path))
