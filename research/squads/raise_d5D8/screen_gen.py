#!/usr/bin/env python3
"""Screen arbitrary haar_gen3 groups for (5,8) by random-S cost statistics (RANDSAMPLE), like screen.py.

Each input line is "N <haar_gen3 group argv> n", e.g. "4896 prod meta 17 12 ... meta ... 1" (the group argv
after N; the last token is the Z_n factor). Output TSV: N, the group argv, min, p1, p10, median. Sorted by p1,
then median.
Usage: screen_gen.py HAAR_GEN3 GROUPS_TXT OUT_TSV [SAMPLES] [WORKERS]
"""
import subprocess, sys, re
from concurrent.futures import ThreadPoolExecutor

HAAR, GROUPS, OUT = sys.argv[1], sys.argv[2], sys.argv[3]
SAMPLES = sys.argv[4] if len(sys.argv) > 4 else "2000"
WORKERS = int(sys.argv[5]) if len(sys.argv) > 5 else 4
pat = re.compile(r"min=(\d+) p1=(\d+) p10=(\d+) median=(\d+)")

def run(line):
    f = line.split()
    N, rest = f[0], f[1:]
    env = {"RANDSAMPLE": SAMPLES, "THREADS": "1", "PATH": "/usr/bin:/bin"}
    try:
        p = subprocess.run(["nice", "-n", "5", "timeout", "300", HAAR, "5", "8", "1", "1", "8",
                            "/dev/null"] + rest, capture_output=True, text=True, env=env)
        mt = pat.search(p.stdout)
        if not mt:
            return None
        return (int(N), " ".join(rest)) + tuple(int(x) for x in mt.groups())
    except Exception:
        return None

lines = [l for l in open(GROUPS) if l.strip()]
with ThreadPoolExecutor(WORKERS) as ex, open(OUT, "w") as f:
    f.write("N\tgroup\tmin\tp1\tp10\tmedian\n")
    for res in ex.map(run, lines):
        if res:
            f.write("\t".join(map(str, res)) + "\n")
            f.flush()
