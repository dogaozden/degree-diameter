"""Exhaustive lift search for one cell over small bases: every base on h+h vertices (h in --hs), every group of
order N = n/(2h) from groups.specs_rich, every voltage assignment (lift.c exhaust). Definitive within that family.

Usage: python3 exhaust_cell.py --delta d --D D --orders LO:HI --hs 2,3 --tag TAG [--maxspace 2e7] [--timeout 1200]
Results: runs/TAG.tsv (n, h, base, group, solutions>0?, best cost, evaluated, seconds); solutions in sols/.
"""
import argparse
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import groups  # noqa: E402
from run_cell import bases_for  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--delta", type=int, required=True)
    ap.add_argument("--D", type=int, required=True)
    ap.add_argument("--orders", required=True)
    ap.add_argument("--hs", default="2,3")
    ap.add_argument("--tag", required=True)
    ap.add_argument("--maxspace", type=float, default=2e7)
    ap.add_argument("--timeout", type=float, default=1200)
    a = ap.parse_args()
    lo, hi = map(int, a.orders.split(":"))
    log = open(os.path.join(HERE, "runs", f"{a.tag}.tsv"), "a")
    for n in range(lo, hi + 1, 2):
        for h in map(int, a.hs.split(",")):
            if n % (2 * h):
                continue
            N = n // (2 * h)
            for b in bases_for(h, a.delta, 0):
                free = sum(1 for l in open(b) if l.startswith("e ")) - (2 * h - 1)
                if N ** free > a.maxspace:
                    continue
                for g in groups.specs_rich(N):
                    out = os.path.join(HERE, "sols", f"{a.tag}_n{n}_{os.path.basename(b)[:-4]}_{g.replace(' ', '')}.txt")
                    t0 = time.time()
                    try:
                        r = subprocess.run([os.path.join(HERE, "lift"), "exhaust", b, str(a.D), out] + g.split(),
                                           capture_output=True, text=True, timeout=a.timeout).stdout
                    except subprocess.TimeoutExpired:
                        r = ""
                    kv = dict(w.split("=", 1) for w in r.split() if "=" in w)
                    sol = kv.get("solutions", "?")
                    line = f"{n}\t{h}\t{os.path.basename(b)[:-4]}\t{g}\t{sol}\t{kv.get('best', '?')}\t{kv.get('evaluated', '?')}\t{time.time() - t0:.1f}"
                    log.write(line + "\n")
                    log.flush()
                    if sol not in ("0", "?"):
                        print("SOLVED", line, flush=True)
    print(f"{a.tag}: done", flush=True)


if __name__ == "__main__":
    main()
