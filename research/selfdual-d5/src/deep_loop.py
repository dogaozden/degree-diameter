#!/usr/bin/env python3
"""deep_loop.py: keep running 300 s sdtabu deep runs (src/deep_tabu.sh) on the near misses (best <= THR) of the K = 9
sweeps above the current record order (logs/K9/RECORD_N), smallest best first, each (group, record, type) once per
seed.  Stops when logs/K9/deep/STOP exists.  env: THR (default 3), SECS (300), SEED (11)."""
import glob, os, subprocess, time
THR = int(os.environ.get("THR", 3)); SECS = os.environ.get("SECS", "300"); SEED = os.environ.get("SEED", "11")
os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
def cands():
    rec = int(open("logs/K9/RECORD_N").read())
    rows = []
    for f in glob.glob("logs/K9/tabu/*.out"):
        n, i = os.path.basename(f)[:-4].split("_")
        if int(n) <= rec: continue
        for l in open(f):
            t = l.split()
            if t and t[0] == "TABU" and int(t[t.index("best") + 1]) <= THR:
                rows.append((int(t[t.index("best") + 1]), int(n), ["sg", n, i, t[2], t[t.index("f") + 1], t[t.index("m") + 1]], f"{n}_{i}_r{t[2]}_f{t[t.index('f') + 1]}"))
    for f in glob.glob("logs/K9/meta/*.out"):
        p, k, d = os.path.basename(f)[:-4].split("_"); n = int(p) * int(k)
        if n <= rec: continue
        for l in open(f):
            t = l.split()
            if t and t[0] == "TABU" and int(t[t.index("best") + 1]) <= THR:
                rows.append((int(t[t.index("best") + 1]), n, ["meta", str(n), p, k, d, t[2], t[t.index("f") + 1], t[t.index("m") + 1]], f"{p}_{k}_{d}_r{t[2]}_f{t[t.index('f') + 1]}"))
    for f in glob.glob("logs/K9/meta2/*.out"):
        p, k, d = os.path.basename(f)[:-4].split("_"); n = int(p) * int(k)
        if n <= rec: continue
        for l in open(f):
            t = l.split()
            if t and t[0] == "TABU" and int(t[t.index("best") + 1]) <= THR:
                rows.append((int(t[t.index("best") + 1]), n, ["meta2", str(n), p, k, d, t[2], t[t.index("f") + 1], t[t.index("m") + 1]], f"c{p}_{k}_{d}_r{t[2]}_f{t[t.index('f') + 1]}"))
    rows.sort(key=lambda r: (r[0], r[1]))
    return rows
done = set(l.strip() for l in open("logs/K9/deep/done.txt")) if os.path.exists("logs/K9/deep/done.txt") else set()
while not os.path.exists("logs/K9/deep/STOP"):
    todo = [r for r in cands() if f"{r[3]}_s{SEED}" not in done]
    if not todo: time.sleep(60); continue
    b, n, args, key = todo[0]
    subprocess.run(["src/deep_tabu.sh"] + args + [SECS, SEED])
    done.add(f"{key}_s{SEED}"); open("logs/K9/deep/done.txt", "a").write(f"{key}_s{SEED}\n")
