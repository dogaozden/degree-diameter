"""Scan many metacyclic groups quickly for one degree, 3 worker processes.

Usage: python3 scan.py d N_lo N_hi secs [kmin] [kmax] [faithful_only=1]
Prints one haar_search line per group; solutions go to sols/d{d}_N{N}_{m}_{k}_{lam}.txt and are
built into graphs/haar_d{d}_n{2N}.json.
"""
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

import drive

HERE = os.path.dirname(os.path.abspath(__file__))


def run(args):
    d, N, m, k, lam, secs = args
    sol = os.path.join(HERE, "sols", f"d{d}_N{N}_{m}_{k}_{lam}.txt")
    r = subprocess.run([os.path.join(HERE, "haar_search"), str(d), str(m), str(k), str(lam),
                        str(N * 7 + lam), str(secs), sol], capture_output=True, text=True)
    line = r.stdout.strip()
    if " best=0 " in line:
        out = os.path.join(HERE, "graphs", f"haar_d{d}_n{2 * N}.json")
        if not os.path.exists(out):
            subprocess.run([sys.executable, os.path.join(HERE, "build_haar.py"), sol, out])
    print(line, flush=True)
    return line


def main():
    d, lo, hi, secs = map(int, sys.argv[1:5])
    kmin = int(sys.argv[5]) if len(sys.argv) > 5 else 3
    kmax = int(sys.argv[6]) if len(sys.argv) > 6 else 12
    faithful = int(sys.argv[7]) if len(sys.argv) > 7 else 1
    jobs = []
    smooth = int(os.environ.get("SMOOTH", "0"))
    for N in range(lo, hi + 1):
        if smooth:
            x, p = N, 2
            while x > 1 and p <= smooth:
                while x % p == 0:
                    x //= p
                p += 1
            if x > 1:
                continue
        for (m, k, lam) in drive.groups(N, kmax):
            if k < kmin:
                continue
            if faithful and drive.mult_order(lam, m) != k:
                continue
            jobs.append((d, N, m, k, lam, secs))
    print(f"# {len(jobs)} groups", flush=True)
    with ThreadPoolExecutor(3) as ex:
        list(ex.map(run, jobs))


if __name__ == "__main__":
    main()
