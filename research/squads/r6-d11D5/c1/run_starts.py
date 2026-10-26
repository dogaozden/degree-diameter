"""Build 8 starts per incidence pattern with kkk.py (KK=1, seed = pattern index, 8 tries) and record the best start."""
import os, re, subprocess, json
DC = "/home/user/degree-diameter/research/d11D5/dc"
HERE = "/home/user/degree-diameter/research/squads/r6-d11D5/c1"
pats = []
for line in open(f"{HERE}/classes.txt"):
    m = re.match(r"\s*(\d+) E=(\d+) PAT=(\S+)", line)
    if m: pats.append((int(m.group(1)), int(m.group(2)), m.group(3)))
rows = []
for idx, E, pat in pats:
    out = f"{HERE}/starts/p{idx:02d}.in"
    r = subprocess.run(["nice", "-n", "10", "timeout", "300", "python3", "kkk.py", "1", str(idx), out, "8"],
                       cwd=DC, env=dict(os.environ, PAT=pat), capture_output=True, text=True)
    open(f"{HERE}/starts/p{idx:02d}.log", "w").write(r.stdout + r.stderr)
    costs = [int(m.group(1)) for m in re.finditer(r"try \d+ cost (\d+)", r.stdout)]
    best = re.search(r"best (\d+) ", r.stdout)
    rows.append({"idx": idx, "E": E, "PAT": pat, "n_ok": len(costs), "costs": costs,
                 "best": int(best.group(1)) if best else None, "file": out if best else None})
    print(idx, E, pat, "ok", len(costs), "best", rows[-1]["best"], flush=True)
json.dump(rows, open(f"{HERE}/starts/summary.json", "w"), indent=1)
