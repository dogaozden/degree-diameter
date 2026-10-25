#!/usr/bin/env python3
"""Screen metacyclic groups for (5,8) by random-S cost statistics (haar_gen3 RANDSAMPLE).

Each group gets SAMPLES random connection sets; the RANDSAMPLE line gives min, p1, p10 and median
of the uncovered counts. Lower is better. Output TSV: N m k r min p1 p10 median (sorted by p1, then median).
Usage: screen.py HAAR_GEN3 GROUPS_TXT OUT_TSV [SAMPLES] [WORKERS]
"""
import subprocess, sys, re
from concurrent.futures import ThreadPoolExecutor

HAAR, GROUPS, OUT = sys.argv[1], sys.argv[2], sys.argv[3]
SAMPLES = sys.argv[4] if len(sys.argv) > 4 else "2000"
WORKERS = int(sys.argv[5]) if len(sys.argv) > 5 else 4
pat = re.compile(r"min=(\d+) p1=(\d+) p10=(\d+) median=(\d+)")

def run(line):
    N, m, k, r = line.split()
    env = {"RANDSAMPLE": SAMPLES, "THREADS": "1", "PATH": "/usr/bin:/bin"}
    try:
        p = subprocess.run(["nice", "-n", "5", "timeout", "120", HAAR, "5", "8", "1", "1", "8",
                            "/dev/null", "meta", m, k, r, "1"], capture_output=True, text=True, env=env)
        mt = pat.search(p.stdout)
        if not mt:
            return None
        return (int(N), int(m), int(k), int(r)) + tuple(int(x) for x in mt.groups())
    except Exception:
        return None

lines = [l for l in open(GROUPS) if l.strip()]
with ThreadPoolExecutor(WORKERS) as ex, open(OUT, "w") as f:
    f.write("N\tm\tk\tr\tmin\tp1\tp10\tmedian\n")
    for res in ex.map(run, lines):
        if res:
            f.write("\t".join(map(str, res)) + "\n")
            f.flush()
