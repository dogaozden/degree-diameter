"""Run configuration, loaded from a TOML file."""
from __future__ import annotations

import tomllib
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class RunConfig:
    run_id: str
    problem: str                     # module path, e.g. "problems.bipartite_dd.problem"
    seed: int
    generations: int
    candidates_per_generation: int
    eval_seeds: list[int]
    time_limit_s: float
    workers: int
    mutator: dict                    # kind ("claude"|"fake"), model, concurrency, timeout_s, max_calls, stop_at
    selection: dict                  # elite_k, roles {role: weight}
    git: dict                        # enabled, push
    runs_dir: str = "runs"
    records_dir: str = "records"
    smoke_time_limit_s: float = 5.0
    seed_programs: list[str] = field(default_factory=list)   # program.py paths (relative to repo_root) imported into generation 0


def load_config(path: str | Path) -> tuple[RunConfig, str]:
    text = Path(path).read_text()
    return RunConfig(**tomllib.loads(text)), text
