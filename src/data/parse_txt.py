# Definitions, Theorems/Lemmas, Fixed Points
from pprint import pprint

import numpy as np

# Theorem class
class Theorem:
    # Theorem has name, possible set of steps, and preamble
    name: str
    statement: str
    steps: list[str]
    preamble: list[str]

    def __init__(self, name: str, statement:str, steps: list[str], preamble: list[str]):
        self.name = name
        self.statement = statement
        self.steps = steps
        self.preamble = preamble

    def __str__(self):
        curr_str = self.name
        for step in self.steps:
            curr_str += " / " + step

        return curr_str

    # Get a random data point from a theorem by randomly picking a number of steps
    # We then return these steps
    def get_random_state(self):
        curr_state = []

        if len(self.steps) > 0:
            num_states = np.random.randint(len(self.steps) + 1)

            for i in range(0, num_states - 1):
                curr_state.append(self.steps[i])

        return curr_state

# List of all docs and keys for import
FILES_ORDER = ['missing.txt', 'tactics.txt', 'division.txt', 'euclide.txt', 'permutation.txt', 'power.txt', 'gcd.txt', 'primes.txt', 'nthroot.txt']
IMPORT_KEYS = ['missing', 'tactics', 'division', 'euclide', 'permutation', 'power', 'gcd', 'primes', 'nthroot']


import_strings = {}

# Gets data from one file
def parse_file(file_name: str, import_strings, file_key, theorems, path):
    
    print("PARSING " + file_name)
    making_theorem = False
    curr_name = ""
    curr_title = ""
    curr_steps = []
    curr_file = []
    file = open(path + file_name, 'r')
    preamble = []

    # Get all lines
    Lines = file.readlines()

    for line in Lines:
        # Skip out comments
        if line.startswith("(*"):
            continue

        # Get imports and add them to preamble
        if line.startswith("Require Import"):
            key = line[len("Require Import") + 1: -2]
            if key in IMPORT_KEYS:
                preamble += import_strings[key]
            else:
                preamble += [line.strip()]
            continue

        # We can skip continues probably and empty lines
        if line.startswith("Export"):
            continue
        if len(line.strip()) == 0:
            continue

        # Otherwise add the line to our data
        curr_file.append(line.strip())

        # Indications to start batching data to put into a block
        if line.startswith("Lemma") or line.startswith("Theorem"):
            making_theorem = True
            curr_title = line.strip()

            index = 0
            if line.startswith("Lemma"):
                index = 6
            else:
                index = 8

            end_index = 0
            while line[end_index] != ":":
                end_index += 1
            curr_name = line[index: end_index]

            continue

        # If we finish a proof, then we make all of the values into a theorem
        if line.startswith("Qed.") and making_theorem:
            making_theorem = False

            new_theorem = Theorem(curr_name, curr_title, curr_steps, preamble)

            # Add theorem and reset
            theorems.append(new_theorem)

            curr_name = ""
            curr_title = ""
            curr_steps = []

        # If in a bathc, add lines to the batch
        if making_theorem:
            curr_steps.append(line.strip())
        

    file.close()

    # Then we store the file as a preamble for futuree imports
    curr_file = preamble + curr_file
    import_strings[file_key] = curr_file

    # for theorem in theorems:
    #     print(theorem.get_random_state())
    #     print("--------------")


# Iterate over all files to get data
def get_all_theorems(path):
    
    theorems: tuple[Theorem] = []
    for i, file_name in enumerate(FILES_ORDER):
        file_key = IMPORT_KEYS[i]
        parse_file(file_name, import_strings, file_key, theorems, path)

    return theorems

# T = get_all_theorems('./txt files/')

# for t in T:
#     pprint(t.statement)

# pprint(T[-10].preamble)