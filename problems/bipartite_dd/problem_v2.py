"""Run-2 case set: solved calibration cases at half weight, more targets."""
from pathlib import Path

from .problem import BipartiteDD

PROBLEM = BipartiteDD(cases_path=Path(__file__).parent / "cases_v2.toml")
