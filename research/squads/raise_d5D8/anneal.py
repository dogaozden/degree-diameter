#!/usr/bin/env python3
"""Anneal haar_gen3 on a list of metacyclic candidates, WORKERS at a time.

Input lines: "N m k r" (order, Z_m x|_r Z_k). Per candidate: haar_gen3 5 8 SECONDS SEED K OUT meta m k r 1.
A cost-0 run writes OUT (haar_gen3 solution file, verified by haar_gen3's own full check). Results are
appended to RESULTS (TSV). Usage: anneal.py HAAR CANDS OUTDIR SECONDS SEED K WORKERS RESULTS
"""
import subprocess, sys, os, re
from concurrent.futures import ThreadPoolExecutor

HAAR, CANDS, OUTDIR, SECS, SEED, K, WORKERS, RES = sys.argv[1:9]
pat = re.compile(r"RESULT .* best=(\d+) evals=(\d+) time=([\d.]+)")
os.makedirs(OUTDIR, exist_ok=True)

def run(line):
    f = line.split()
    N, m, k, r = f[:4]
    n = f[4] if len(f) > 4 else "1"
    tag = f"N{N}_m{m}_k{k}_r{r}_n{n}_s{SEED}"
    out = os.path.join(OUTDIR, f"sol_{tag}.txt")
    log = os.path.join(OUTDIR, f"log_{tag}.txt")
    env = dict(os.environ, THREADS="1")
    with open(log, "w") as lf:
        p = subprocess.run(["nice", "-n", "5", "timeout", str(int(float(SECS)) + 120), HAAR, "5", "8", SECS, SEED,
                            K, out, "meta", m, k, r, n], stdout=subprocess.PIPE, stderr=lf, text=True, env=env)
    mt = pat.search(p.stdout)
    best = mt.group(1) if mt else "NA"
    solved = os.path.exists(out) and os.path.getsize(out) > 0
    return f"{N}\t{m}\t{k}\t{r}\t{n}\t{SEED}\t{best}\t{'SOLVED' if solved else 'no'}\t{p.stdout.strip().splitlines()[-1] if p.stdout.strip() else ''}"

lines = [l for l in open(CANDS) if l.strip()]
with ThreadPoolExecutor(int(WORKERS)) as ex, open(RES, "a") as f:
    for res in ex.map(run, lines):
        f.write(res + "\n"); f.flush()
