"""Make a second wave of cloud islands: one twin per island, seeded from that island's current best programs.

For each island: read every candidate's fitness from its freshest branch, copy the top 5 programs to
seeds/wave2/<island>/<cid>.py, and write configs/<island>-w2.toml (same settings, new run_id and seed).
Run from the repo root after `git fetch --all`.
"""
import json, re, subprocess
from pathlib import Path

ISLANDS = ["island-1", "spec-d4d5", "spec-d5d5", "spec-d6d5", "spec-d7d5", "spec-d7d4", "spec-d11d4", "spec-d3fam",
           "spec-d16d3", "c-d4d5", "c-d5d5", "c-d6d5", "c-d7d5", "c-d7d4", "c-d11d4", "c-d3fam", "c-d16d3"]
TOP = 5


def git(*a, inp=None):
    return subprocess.run(["git", *a], capture_output=True, text=True, check=True, input=inp).stdout


def freshest(run_id):
    refs = [l.rsplit(" ", 1) for l in git("for-each-ref", "--format=%(refname:short) %(committerdate:unix)",
                                          f"refs/remotes/origin/{run_id}", f"refs/remotes/origin/claude/{run_id}-evolve-run-*").splitlines()]
    return max(refs, key=lambda r: int(r[1]))[0]


for run_id in ISLANDS:
    ref = freshest(run_id)
    scored = []
    for line in git("ls-tree", "-r", ref, f"runs/{run_id}/candidates/").splitlines():
        info, path = line.split("\t")
        if path.endswith("/result.json"):
            res = json.loads(git("cat-file", "-p", info.split()[2]))
            scored.append((res.get("fitness", 0.0), path.split("/")[3]))
    scored.sort(reverse=True)
    out = Path("seeds/wave2") / run_id
    out.mkdir(parents=True, exist_ok=True)
    seeds = []
    for fit, cid in scored[:TOP]:
        dst = out / f"{cid}.py"
        dst.write_text(git("show", f"{ref}:runs/{run_id}/candidates/{cid}/program.py"))
        seeds.append(str(dst))
    cfg = Path(f"configs/{run_id}.toml").read_text()
    cfg = re.sub(r'^run_id = ".*"$', f'run_id = "{run_id}-w2"', cfg, count=1, flags=re.M)
    cfg = re.sub(r'^seed = (\d+)$', lambda m: f"seed = {int(m.group(1)) + 1000}", cfg, count=1, flags=re.M)
    cfg = re.sub(r'^seed_programs = \[.*?\]', "seed_programs = [\n" + "".join(f'  "{s}",\n' for s in seeds) + "]",
                 cfg, count=1, flags=re.M | re.S)
    cfg = f"# Wave 2 twin of {run_id}, seeded with its top {TOP} programs as of {ref}.\n" + cfg
    Path(f"configs/{run_id}-w2.toml").write_text(cfg)
    print(f"{run_id}-w2: top fitness {[round(f, 4) for f, _ in scored[:TOP]]}")
