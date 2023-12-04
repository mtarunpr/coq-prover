class Fringe:
    def __init__(self, goals):
        self.goals = goals  # list of goals that all need to be proven for the fringe to be proven; note that each goal also contains a list of hypotheses


class Action:
    def __init__(self, fringe_idx, tactic_idx):
        self.fringe_idx = fringe_idx
        self.tactic = tactic_idx


class State:
    def __init__(self, fringes):
        self.fringes = fringes  # list of fringes, where any one fringe needs to be proven for the state to be proven
