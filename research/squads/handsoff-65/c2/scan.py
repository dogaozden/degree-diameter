#!/usr/bin/env python3
"""Screen (group, base) pairs with shared/tabu. usage: scan.py P MODE BASESEED SECS OUT.tsv GROUP.txt [GROUP.txt ...]
Each group gets one random base (mkbase, seed BASESEED + index). Tabu runs SECS seconds (INIT=random, SEED=1).
Appends "P MODE BASESEED m group best steps secs" to OUT.tsv. Edges of any run that reaches 0 are saved in hits/."""
import os, random, subprocess, sys, re, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mkbase import make
HERE = os.path.dirname(os.path.abspath(__file__))
TABU = os.path.join(HERE, "..", "shared", "tabu")

def write_base(p, mode, seed, path):
    rng = random.Random(seed)
    M = make(p, mode, rng)
    edges = []
    for i in range(p):
        for j in range(p):
            edges += [(i, p + j)] * M[i][j]
    with open(path, "w") as f:
        f.write(f"{2*p} {len(edges)}\n" + " ".join(["0"] * p + ["1"] * p) + "\n")
        for u, w in edges:
            f.write(f"{u} {w} 0\n")

def main():
    p, mode, bseed, secs = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), float(sys.argv[4])
    out = sys.argv[5]
    groups = sys.argv[6:]
    os.makedirs(os.path.join(HERE, "bases"), exist_ok=True)
    os.makedirs(os.path.join(HERE, "hits"), exist_ok=True)
    for gi, g in enumerate(groups):
        with open(g) as f:
            m = int(f.readline())
        name = os.path.basename(g).replace(".txt", "")
        bpath = os.path.join(HERE, "bases", f"p{p}_{mode}_{bseed+gi}.base")
        write_base(p, mode, bseed + gi, bpath)
        env = dict(os.environ, SECS=str(secs), SEED="1", INIT="random")
        hit = os.path.join(HERE, "hits", f"p{p}_m{m}_{name}_b{bseed+gi}.edges")
        t0 = time.time()
        try:
            r = subprocess.run(["nice", "-n", "10", TABU, bpath, g, hit], env=env, capture_output=True, text=True,
                               timeout=secs + 120)
            res = re.search(r"RESULT best (\d+) steps (\d+)", r.stdout)
            best, steps = (int(res.group(1)), int(res.group(2))) if res else (-1, -1)
        except subprocess.TimeoutExpired:
            best, steps = -2, -2
        line = f"{p}\t{mode}\t{bseed+gi}\t{m}\t{name}\t{best}\t{steps}\t{time.time()-t0:.0f}\n"
        with open(os.path.join(HERE, out), "a") as f:
            f.write(line)
        if best != 0 and os.path.exists(hit):
            os.remove(hit)
        if best == 0:
            print("HIT", line, flush=True)

if __name__ == "__main__":
    main()
