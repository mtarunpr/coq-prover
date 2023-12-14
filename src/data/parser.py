# Definitions, Theorems/Lemmas, Fixpoints, etc.
from pathlib import Path
from .coq import Theorem


# List of all docs and keys for import
FILES_ORDER = [
    "missing.v",
    "tactics.v",
    "division.v",
    # "euclide.v",
    # "permutation.v",
    # "power.v",
    # "gcd.v",
    # "primes.v",
    # "nthroot.v",
]
IMPORT_KEYS = [
    "missing",
    "tactics",
    "division",
    # "euclide",
    # "permutation",
    # "power",
    # "gcd",
    # "primes",
    # "nthroot",
]


import_strings = {}
keywords_map = {}


# Gets data from one file
def parse_file(
    file_name: str, import_strings, file_key, theorems, path: Path, keywords_map
):
    print("PARSING " + file_name)
    making_theorem = False
    curr_name = ""
    curr_title = ""
    curr_steps = []
    curr_file = []
    file = open(path / file_name, "r")
    preamble = []
    curr_keywords = []

    # Get all lines
    lines = file.readlines()

    for line in lines:
        # Skip out comments
        if line.startswith("(*"):
            continue

        # Get imports and add them to preamble
        if any(
            line.startswith(imp_type) for imp_type in ["Require", "Import", "Export"]
        ):
            key = line.split(" ")[-1].strip()[:-1]
            if key in IMPORT_KEYS:
                preamble += import_strings[key]
                curr_keywords += keywords_map[key]
            else:
                preamble += [line.strip()]
            continue

        # We can skip empty lines
        if len(line.strip()) == 0:
            continue

        # Otherwise add the line to our data
        curr_file.append(line.strip())

        if line.startswith("Fact"):
            index = 5
            end_index = index + 1
            while line[end_index] != ":":
                end_index += 1
            keyword = line[index:end_index]
            keyword = keyword.strip()
            curr_keywords.append(keyword)
            # print(keyword)
            continue

        if line.startswith("Definition"):
            index = 11
            end_index = index + 1
            while line[end_index] != "(":
                end_index += 1
            keyword = line[index:end_index]
            keyword = keyword.strip()
            curr_keywords.append(keyword)
            # print(keyword)
            continue

        if line.startswith("Fixpoint"):
            index = 9
            end_index = index + 1
            while line[end_index] != "(":
                end_index += 1
            keyword = line[index:end_index]
            keyword = keyword.strip()
            curr_keywords.append(keyword)
            # print(keyword)
            continue

        # Indications to start batching data to put into a block
        if line.startswith("Lemma") or line.startswith("Theorem"):
            making_theorem = True
            # Store copy of file until before this line so we can add to this theorem's preamble
            file_before_theorem = curr_file.copy()[:-1]
            curr_title = line.strip()

            index = 0
            if line.startswith("Lemma"):
                index = 6
            else:
                index = 8

            end_index = 0
            while line[end_index] != ":":
                end_index += 1
            curr_name = line[index:end_index]
            curr_name = curr_name.strip()

            continue

        # If we finish a proof, then we make all of the values into a theorem
        if line.startswith("Qed.") and making_theorem:
            making_theorem = False

            new_theorem = Theorem(
                curr_name,
                curr_title,
                curr_steps,
                preamble + file_before_theorem,
                curr_keywords,
            )

            # Add theorem and reset
            theorems.append(new_theorem)
            curr_keywords.append(curr_name)

            curr_name = ""
            curr_title = ""
            curr_steps = []

        # If in a batch, add lines to the batch
        if making_theorem:
            curr_steps.append(line.strip())

    file.close()

    # Then we store the file as a preamble for future imports
    import_strings[file_key] = preamble + curr_file
    keywords_map[file_key] = curr_keywords

    # for theorem in theorems:
    #     print(theorem.get_random_state())
    #     print("--------------")


# Iterate over all files to get data
def get_all_theorems(path: Path):
    theorems: tuple[Theorem] = []
    for i, file_name in enumerate(FILES_ORDER):
        file_key = IMPORT_KEYS[i]
        parse_file(file_name, import_strings, file_key, theorems, path, keywords_map)

    return theorems


if __name__ == "__main__":
    theorems = get_all_theorems(Path(__file__).parent / "raw")
    print(theorems[-10].name)
    print(theorems[-10].statement)
    print(theorems[-10].preamble)
