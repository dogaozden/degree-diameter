"""Durable, append-only run store. Every write is atomic so a restart can rebuild state from files."""
from __future__ import annotations

import json
import os
import tempfile
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path


@dataclass
class CandidateRecord:
    id: str
    generation: int
    parents: list[str]
    role: str
    fitness: float | None              # None until evaluated
    case_values: dict[str, float]      # case_id -> value (0 if invalid); {} until evaluated
    case_scores: dict[str, float]


def _atomic_write(path: Path, text: str) -> None:
    """Write text to path via a temp file in the same directory plus rename."""
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=path.parent, prefix=path.name + ".", suffix=".tmp")
    try:
        with os.fdopen(fd, "w") as f:
            f.write(text)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
    except BaseException:
        Path(tmp).unlink(missing_ok=True)
        raise


def _write_json(path: Path, obj: dict) -> None:
    _atomic_write(path, json.dumps(obj, indent=2, sort_keys=True) + "\n")


def _read_json_or_none(path: Path) -> dict | None:
    if not path.exists():
        return None
    return json.loads(path.read_text())


class RunStore:
    def __init__(self, root: Path):
        self.root = Path(root)

    def init(self, config_text: str) -> None:
        (self.root / "candidates").mkdir(parents=True, exist_ok=True)
        (self.root / "generations").mkdir(parents=True, exist_ok=True)
        config = self.root / "config.toml"
        if not config.exists():
            _atomic_write(config, config_text)

    # candidates

    def candidate_dir(self, cid: str) -> Path:
        return self.root / "candidates" / cid

    def program_path(self, cid: str) -> Path:
        return self.candidate_dir(cid) / "program.py"

    def _meta_path(self, cid: str) -> Path:
        return self.candidate_dir(cid) / "meta.json"

    def _result_path(self, cid: str) -> Path:
        return self.candidate_dir(cid) / "result.json"

    def add_candidate(self, cid: str, code: str, meta: dict) -> None:
        if self.has_candidate(cid):
            raise FileExistsError(f"candidate {cid} already exists")
        meta = dict(meta)
        meta.setdefault("created", datetime.now(timezone.utc).isoformat())
        _atomic_write(self.program_path(cid), code)
        _write_json(self._meta_path(cid), meta)  # written last: its presence marks the candidate as real

    def has_candidate(self, cid: str) -> bool:
        return self._meta_path(cid).exists()

    def read_program(self, cid: str) -> str:
        return self.program_path(cid).read_text()

    def read_meta(self, cid: str) -> dict:
        return json.loads(self._meta_path(cid).read_text())

    def has_result(self, cid: str) -> bool:
        return self._result_path(cid).exists()

    def write_result(self, cid: str, result: dict) -> None:
        _write_json(self._result_path(cid), result)

    def read_result(self, cid: str) -> dict:
        return json.loads(self._result_path(cid).read_text())

    def _candidate_ids(self) -> list[str]:
        base = self.root / "candidates"
        if not base.exists():
            return []
        return sorted(p.name for p in base.iterdir() if (p / "meta.json").exists())

    def load_candidates(self) -> list[CandidateRecord]:
        records = []
        for cid in self._candidate_ids():
            meta = self.read_meta(cid)
            fit, values, scores = None, {}, {}
            if self.has_result(cid):
                result = self.read_result(cid)
                fit = result["fitness"]
                values = {k: v["value"] for k, v in result["cases"].items()}
                scores = {k: v["score"] for k, v in result["cases"].items()}
            records.append(CandidateRecord(
                id=meta["id"], generation=meta["generation"], parents=list(meta["parents"]),
                role=meta["role"], fitness=fit, case_values=values, case_scores=scores))
        return records

    def candidates_in_generation(self, g: int) -> list[str]:
        return [cid for cid in self._candidate_ids() if self.read_meta(cid)["generation"] == g]

    # generations and plans

    def _generation_path(self, g: int) -> Path:
        return self.root / "generations" / f"{g:03d}.json"

    def _plan_path(self, g: int) -> Path:
        return self.root / "generations" / f"{g:03d}.plan.json"

    def generation_done(self, g: int) -> bool:
        summary = self.read_generation(g)
        return bool(summary and summary.get("complete") is True)

    def write_generation(self, g: int, summary: dict) -> None:
        _write_json(self._generation_path(g), summary)

    def read_generation(self, g: int) -> dict | None:
        return _read_json_or_none(self._generation_path(g))

    def write_plan(self, g: int, plan: dict) -> None:
        _write_json(self._plan_path(g), plan)

    def read_plan(self, g: int) -> dict | None:
        return _read_json_or_none(self._plan_path(g))

    # logs

    def append_call(self, record: dict) -> None:
        self.root.mkdir(parents=True, exist_ok=True)
        with open(self.root / "calls.jsonl", "a") as f:
            f.write(json.dumps(record, sort_keys=True) + "\n")
            f.flush()
            os.fsync(f.fileno())

    def count_calls(self) -> int:
        path = self.root / "calls.jsonl"
        if not path.exists():
            return 0
        with open(path) as f:
            return sum(1 for line in f if line.strip())

    def write_status(self, text: str) -> None:
        _atomic_write(self.root / "status.md", text)
