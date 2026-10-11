"""Make a new wave of cloud islands: for each (source island, new run id) pair, copy the source's config
with a new run id and seed, seeded with the source's top 5 programs.

Usage: python scripts/make_wave.py WAVE SEED_OFFSET SOURCE[:BASE] ...
  WAVE         suffix for the new run ids and the seeds folder, e.g. w3
  SEED_OFFSET  added to the base config's seed
  SOURCE       island whose best programs seed the new island (e.g. c-d5d5-w2)
  BASE         config the new island copies its settings from (default: SOURCE's own config)
New run id: BASE + "-" + WAVE + ("b" if SOURCE ends in -w2 else "").
Run from the repo root after `git fetch --all`.
"""
import json, re, subprocess, sys
from pathlib import Path

TOP = 5


def git(*a):
    return subprocess.run(["git", *a], capture_output=True, text=True, check=True).stdout


def freshest(run_id):
    refs = [l.rsplit(" ", 1) for l in git("for-each-ref", "--format=%(refname:short) %(committerdate:unix)",
                                          f"refs/remotes/origin/{run_id}", f"refs/remotes/origin/claude/{run_id}-evolve-run-*").splitlines()]
    return max(refs, key=lambda r: int(r[1]))[0]


wave, offset = sys.argv[1], int(sys.argv[2])
for spec in sys.argv[3:]:
    source, _, base = spec.partition(":")
    base = base or source
    new_id = f"{base}-{wave}{'b' if source.endswith('-w2') else ''}"
    ref = freshest(source)
    scored = []
    for line in git("ls-tree", "-r", ref, f"runs/{source}/candidates/").splitlines():
        info, path = line.split("\t")
        if path.endswith("/result.json"):
            scored.append((json.loads(git("cat-file", "-p", info.split()[2])).get("fitness", 0.0), path.split("/")[3]))
    scored.sort(reverse=True)
    out = Path("seeds") / wave / new_id
    out.mkdir(parents=True, exist_ok=True)
    seeds = []
    for fit, cid in scored[:TOP]:
        dst = out / f"{source}-{cid}.py"
        dst.write_text(git("show", f"{ref}:runs/{source}/candidates/{cid}/program.py"))
        seeds.append(str(dst))
    cfg = Path(f"configs/{base}.toml").read_text()
    cfg = re.sub(r'^run_id = ".*"$', f'run_id = "{new_id}"', cfg, count=1, flags=re.M)
    cfg = re.sub(r'^seed = (\d+)$', lambda m: f"seed = {int(m.group(1)) + offset}", cfg, count=1, flags=re.M)
    cfg = re.sub(r'^seed_programs = \[.*?\]', "seed_programs = [\n" + "".join(f'  "{s}",\n' for s in seeds) + "]",
                 cfg, count=1, flags=re.M | re.S)
    Path(f"configs/{new_id}.toml").write_text(f"# Wave {wave} island, seeded with the top {TOP} programs of {source} ({ref}).\n" + cfg)
    print(f"{new_id}: from {source}, top fitness {[round(f, 4) for f, _ in scored[:TOP]]}")
