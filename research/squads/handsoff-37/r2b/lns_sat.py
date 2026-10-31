#!/usr/bin/env python3
"""lns_sat.py (r2b): LNS with an exact SAT inner solver (region re-solve, see satreg.py).

Each step: pick a region (balls of radius RAD around 1-2 centres, centres chosen near far pairs or
at random), solve exactly for a rewiring with far <= T (T = cur-1 for descent, T = cur for plateau
moves), verify the result with bin/score37, accept it. Logs every step to LOG (append).

Usage: lns_sat.py START.edges OUTDIR RAD STEPS SEED PLATEAU_PROB SOLVER TLIM_PER_SOLVE
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
    far = int(out.split("far=")[1].split()[0])
    return far, out


def write(fn, n, edges):
    with open(fn, "w") as f:
        f.write(f"{n}\n")
        for a, b in edges:
            f.write(f"{a} {b}\n")


def main():
    start, outdir, rad, steps, seed, pplat, solver = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), float(sys.argv[6]), sys.argv[7]
    os.makedirs(outdir, exist_ok=True)
    rnd = random.Random(seed)
    tmp = os.path.join(outdir, f"tmp_{seed}.edges")
    n, adj = satreg.load(start)
    cur_far, _ = score(start)
    cur_edges = [(v, w) for v in range(n) for w in adj[v] if v < w]
    best = cur_far
    logf = open(os.path.join(outdir, f"log_{seed}.txt"), "a")
    print(f"start far {cur_far} n {n}", file=logf, flush=True)
    for step in range(steps):
        col = [c % 2 for c in satreg.bfs(adj, 0)]
        # far vertices (pairs at distance >= 8 by score37 convention, computed by BFS)
        far_vs = []
        for s in range(n):
            d = satreg.bfs(adj, s)
            if any(d[t] < 0 or d[t] > 7 for t in range(n) if t != s):
                far_vs.append(s)
        k = 1 if rnd.random() < 0.5 else 2
        centres = [rnd.choice(far_vs)] + ([rnd.randrange(n)] if k == 2 else [])
        T = cur_far if rnd.random() < pplat else cur_far - 1
        S = satreg.region_of(n, adj, centres, rad)
        t0 = time.time()
        ok, edges = satreg.build_and_solve(n, adj, col, S, T, solver, verbose=False)
        dt = time.time() - t0
        print(f"step {step} centres {centres} |S| {len(S)} T {T} -> {'SAT' if ok else 'UNSAT/none'} {dt:.1f}s", file=logf, flush=True)
        if not ok or edges is None:
            continue
        write(tmp, n, edges)
        far_new, line = score(tmp)
        if far_new > T:
            print(f"  VERIFY MISMATCH far {far_new} > T {T}: {line}", file=logf, flush=True)
            continue
        if not all(len(satreg.load(tmp)[1][v]) == 3 for v in range(n)):
            print("  not cubic", file=logf, flush=True)
            continue
        n, adj = satreg.load(tmp)
        cur_far = far_new
        print(f"  accepted far {cur_far}", file=logf, flush=True)
        if cur_far < best:
            best = cur_far
            write(os.path.join(outdir, f"best{best}_seed{seed}.edges"), n, edges)
            print(f"NEW BEST {best}", file=logf, flush=True)
            if best == 0:
                break
    print(f"done best {best} cur {cur_far}", file=logf, flush=True)


if __name__ == "__main__":
    main()
