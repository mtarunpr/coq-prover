import numpy as np

class Theorem:
    # Theorem has name, statement, possible set of steps, and preamble
    name: str
    statement: str
    steps: list[str]
    preamble: list[str]

    # Given a preamble, we want to get a list of all facts, definitions, fixed points, theorems, lemmas, etc
    # We just want the name
    keywords: list[str]

    def __init__(
        self,
        name: str,
        statement: str,
        steps: list[str],
        preamble: list[str],
        keywords: list[str],
    ):
        self.name = name
        self.statement = statement
        self.steps = steps
        self.preamble = preamble
        self.keywords = keywords

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
