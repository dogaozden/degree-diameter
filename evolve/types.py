"""Types shared by the engine and problem plug-ins."""
from __future__ import annotations

import importlib
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Protocol


class CheckerBug(Exception):
    """A checked value exceeded the case's proven ceiling: the checker is wrong. Stops the run."""


@dataclass(frozen=True)
class Case:
    id: str
    params: dict          # passed as build(**params, seed=..., time_limit=...)
    record: float         # best known value (score = value / record)
    ceiling: float        # proven upper bound; value > ceiling => CheckerBug
    kind: str             # "calibration" | "target"
    weight: float


@dataclass(frozen=True)
class CaseScore:
    case_id: str
    status: str           # "ok" | "timeout" | "crash" | "bad_output"
    valid: bool
    value: float          # 0.0 if not valid
    score: float          # value / record, 0.0 if not valid
    reason: str           # "" if valid
    wall_s: float


class Problem(Protocol):
    name: str
    cases: list[Case]
    harness_dir: Path     # put on sys.path for candidates
    seed_program: Path

    def evaluate(self, case: Case, output: Any) -> tuple[bool, float, str]: ...
    def verify(self, case: Case, output: Any) -> bool: ...
    def prompt_context(self) -> str: ...
    def smoke_case(self) -> Case: ...


def load_problem(module_path: str) -> Problem:
    """Load `module.PROBLEM`, or `module:NAME` to pick another attribute (e.g. one island's problem)."""
    module, _, attr = module_path.partition(":")
    return getattr(importlib.import_module(module), attr or "PROBLEM")
