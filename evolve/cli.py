"""Command line: `python -m evolve run CONFIG [--fake]` and `python -m evolve status RUN_DIR`."""
from __future__ import annotations

import argparse
from pathlib import Path

from evolve.config import load_config
from evolve.loop import run


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="evolve")
    sub = parser.add_subparsers(dest="cmd", required=True)
    p_run = sub.add_parser("run", help="run (or resume) an evolution run")
    p_run.add_argument("config")
    p_run.add_argument("--fake", action="store_true", help="use the fake mutator instead of calling claude")
    p_status = sub.add_parser("status", help="print a run's status.md")
    p_status.add_argument("run_dir")
    args = parser.parse_args(argv)

    if args.cmd == "status":
        path = Path(args.run_dir) / "status.md"
        if not path.exists():
            print(f"no status.md in {args.run_dir}")
            return 1
        print(path.read_text())
        return 0

    cfg, text = load_config(args.config)
    if args.fake:
        cfg.mutator = {**cfg.mutator, "kind": "fake"}
    return run(cfg, text, Path.cwd(), log=lambda *a: print(*a, flush=True))
