"""Specialist islands: each searches only a few target cases, so it tests far more programs per CPU.

Pick one in a config with  problem = "problems.bipartite_dd.islands:D7D4"
"""
from pathlib import Path

from evolve.types import Case

from .problem import BipartiteDD

_V2 = Path(__file__).parent / "cases_v2.toml"
_SMOKE_WEIGHT = 0.1   # d3D3 stays in every island as the cheap smoke case


class Specialist(BipartiteDD):
    def __init__(self, targets):
        super().__init__(cases_path=_V2)
        by_id = {c.id: c for c in self.cases}
        smoke = by_id["d3D3"]
        self.cases = [Case(smoke.id, smoke.params, smoke.record, smoke.ceiling, smoke.kind, _SMOKE_WEIGHT)]
        self.cases += [by_id[t] for t in targets]
        self.targets = list(targets)

    def prompt_context(self):
        focus = ", ".join(f"d={c.params['d']} D={c.params['D']} (record {c.record:g})" for c in self.cases[1:])
        return super().prompt_context() + (
            f"\n\n## This island's focus\nOnly these targets are scored here: {focus}. "
            "d3D3 is only a quick sanity case. Spend nearly all of time_limit searching for the targets, "
            "and aim to BEAT the record, not just match it.\n")


D4D5 = Specialist(["d4D5"])
D5D5 = Specialist(["d5D5"])
D6D5 = Specialist(["d6D5"])
D7D5 = Specialist(["d7D5"])
D10D5 = Specialist(["d10D5"])
D11D5 = Specialist(["d11D5"])
D7D4 = Specialist(["d7D4"])
D11D4 = Specialist(["d11D4"])
D3FAM = Specialist(["d11D3", "d13D3", "d15D3"])
D16D3 = Specialist(["d16D3"])
