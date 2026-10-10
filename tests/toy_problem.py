"""A tiny problem for engine tests: build(x) should return a big number."""
from pathlib import Path

from evolve.types import Case, CheckerBug

_DIR = Path(__file__).parent / "toy_lib"


class Toy:
    name = "toy"
    cases = [
        Case("c1", {"x": 3}, record=6, ceiling=100, kind="calibration", weight=1),
        Case("c2", {"x": 5}, record=10, ceiling=100, kind="target", weight=2),
    ]
    harness_dir = _DIR
    seed_program = _DIR / "seed.py"

    def evaluate(self, case, output):
        if isinstance(output, bool) or not isinstance(output, (int, float)):
            return (False, 0.0, "malformed: not a number")
        if output > case.ceiling:
            raise CheckerBug(f"{case.id}: {output} > ceiling {case.ceiling}")
        return (True, float(output), "")

    def verify(self, case, output):
        return isinstance(output, (int, float)) and not isinstance(output, bool) and output <= case.ceiling

    def prompt_context(self):
        return "Toy problem: return a big number."

    def smoke_case(self):
        return self.cases[0]


PROBLEM = Toy()
