#!/usr/bin/env python3
"""Anneal haar_gen3 on arbitrary group candidates, WORKERS at a time (generalises anneal.py).

Input lines: "N <haar_gen3 group argv> n" (as written by enum_prod.py / screen_gen.py, e.g.
"4896 prod meta 17 12 ... 1"). Per candidate: haar_gen3 5 8 SECONDS SEED K OUT <group argv>.
A cost-0 run writes OUT (haar_gen3 solution file; haar_gen3 has checked the full diameter itself).
Results are appended to RESULTS as TSV: N, group argv, seed, best, solved, last RESULT line.
Usage: anneal_gen.py HAAR CANDS OUTDIR SECONDS SEED K WORKERS RESULTS
"""
import subprocess, sys, os, re, hashlib
from concurrent.futures import ThreadPoolExecutor

HAAR, CANDS, OUTDIR, SECS, SEED, K, WORKERS, RES = sys.argv[1:9]
pat = re.compile(r"RESULT .* best=(\d+) evals=(\d+) time=([\d.]+)")
os.makedirs(OUTDIR, exist_ok=True)

def run(line):
    f = line.split()
    N, rest = f[0], f[1:]
    tag = f"N{N}_" + hashlib.md5(" ".join(rest).encode()).hexdigest()[:10] + f"_s{SEED}"
    out = os.path.join(OUTDIR, f"sol_{tag}.txt")
    log = os.path.join(OUTDIR, f"log_{tag}.txt")
    env = dict(os.environ, THREADS="1")
    with open(log, "w") as lf:
        p = subprocess.run(["nice", "-n", "5", "timeout", str(int(float(SECS)) + 120), HAAR, "5", "8", SECS, SEED,
                            K, out] + rest, stdout=subprocess.PIPE, stderr=lf, text=True, env=env)
    mt = pat.search(p.stdout)
    best = mt.group(1) if mt else "NA"
    solved = os.path.exists(out) and os.path.getsize(out) > 0
    last = p.stdout.strip().splitlines()[-1] if p.stdout.strip() else ""
    return f"{N}\t{' '.join(rest)}\t{SEED}\t{best}\t{'SOLVED' if solved else 'no'}\t{last}"

lines = [l for l in open(CANDS) if l.strip()]
with ThreadPoolExecutor(int(WORKERS)) as ex, open(RES, "a") as f:
    for res in ex.map(run, lines):
        f.write(res + "\n"); f.flush()
