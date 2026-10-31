#!/usr/bin/env python3
"""sat_walk.py (r2b): plateau walk / descent with exact SAT region re-solves (diversified by forbidding
some current region edges as assumptions, so each step is a different equal-or-better rewiring).

Usage: sat_walk.py START.edges OUTDIR RAD STEPS SEED TLIM NFORBID [SOLVER]
Each step: random region (ball of radius RAD around a far vertex or a random vertex), T = cur (plateau)
with NFORBID of the region's current edges forbidden, or T = cur-1 (descent) every 4th step.
Verifies with bin/score37 and accepts when far <= T. Log: OUTDIR/log_SEED.txt.
"""
import os
import random
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import satreg  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
SCORE = os.path.join(HERE, "..", "bin", "score37")


def score(fn):
    out = subprocess.run([SCORE, fn], capture_output=True, text=True).stdout.strip()
    return int(out.split("far=")[1].split()[0]), out


def write(fn, n, edges):
    with open(fn, "w") as f:
        f.write(f"{n}\n")
        for a, b in edges:
            f.write(f"{a} {b}\n")


def main():
    start, outdir = sys.argv[1], sys.argv[2]
    rad, steps, seed = int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    tlim, nforbid = float(sys.argv[6]), int(sys.argv[7])
    solver = sys.argv[8] if len(sys.argv) > 8 else "cd19"
    os.makedirs(outdir, exist_ok=True)
    rnd = random.Random(seed)
    tmp = os.path.join(outdir, f"tmp_{seed}.edges")
    n, adj = satreg.load(start)
    cur, _ = score(start)
    best = cur
    logf = open(os.path.join(outdir, f"log_{seed}.txt"), "a")
    print(f"start far {cur} n {n} rad {rad} tlim {tlim} nforbid {nforbid}", file=logf, flush=True)
    stats = {"sat": 0, "unsat": 0, "timeout": 0, "acc": 0, "mismatch": 0}
    for step in range(steps):
        col = [c % 2 for c in satreg.bfs(adj, 0)]
        far_vs = []
        for s in range(n):
            d = satreg.bfs(adj, s)
            if any(d[t] < 0 or d[t] > 7 for t in range(n) if t != s):
                far_vs.append(s)
        centre = rnd.choice(far_vs) if rnd.random() < 0.5 else rnd.randrange(n)
        S = satreg.region_of(n, adj, [centre], rad)
        Sset = set(S)
        inner = [(v, w) for v in S for w in adj[v] if w in Sset and v < w]
        descent = (step % 4 == 3)
        T = cur - 1 if descent else cur
        forbid = []
        if not descent and nforbid > 0 and inner:
            pick = rnd.sample(inner, min(nforbid, len(inner)))
            forbid = [(a, b) if col[a] == 0 else (b, a) for (a, b) in pick]
        t0 = time.time()
        ok, edges = satreg.build_and_solve(n, adj, col, S, T, solver, verbose=False, tlim=tlim, forbid=forbid)
        dt = time.time() - t0
        if ok is None:
            stats["timeout"] += 1
            res = "TIMEOUT"
        elif ok is False:
            stats["unsat"] += 1
            res = "UNSAT"
        else:
            stats["sat"] += 1
            res = "SAT"
        print(f"step {step} centre {centre} |S| {len(S)} T {T} forbid {len(forbid)} -> {res} {dt:.1f}s "
              f"cur {cur}", file=logf, flush=True)
        if not ok or edges is None:
            continue
        write(tmp, n, edges)
        far_new, line = score(tmp)
        if far_new > T:
            stats["mismatch"] += 1
            print(f"  MISMATCH far {far_new} > T {T}: {line}", file=logf, flush=True)
            continue
        n, adj = satreg.load(tmp)
        cur = far_new
        stats["acc"] += 1
        if cur < best:
            best = cur
            write(os.path.join(outdir, f"best{best}_seed{seed}.edges"), n, edges)
            print(f"NEW BEST {best}", file=logf, flush=True)
            if best == 0:
                break
    print(f"done best {best} cur {cur} stats {stats}", file=logf, flush=True)


if __name__ == "__main__":
    main()
