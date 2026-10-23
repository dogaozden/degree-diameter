"""Job lists for haar_gen3 (wave 3): all group families with order N = |M| * n in [lo, hi].

  python3 make_jobs3.py d D lo hi seconds [--seeds S] [--nmax NMAX] [--fam sl,psl,pgl,prod,agl1,meta] [--qmax Q]
Families M: sl/psl/pgl(2,q), q a prime or prime power; tpgl q (Z_n x| PGL(2,q), twisted); csl q (central product
(SL(2,q) x Z_n)/<(-I,n/2)>, n even); prod of two PSL/SL(2,q) (small q); agl1 q.
Each line is batch.sh format: d D seconds seed K group... n, sorted by N (smallest first).
Run with:  BIN=./haar_gen3 bash batch.sh JOBFILE
--best F keeps the fraction F of candidates with the lowest small-order score (group_score.py: few involutions and
elements of order 3..6 = few short cycles); --maxscore X drops candidates scoring above X.  Families group_score
cannot rate (agl1, tpgl, csl) are kept only when --best/--maxscore are not given.
"""
import argparse
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from group_score import group_counts, score

def is_prime(n):
    return n > 1 and all(n % t for t in range(2, int(n ** .5) + 1))

def prime_powers(qmax):
    out = []
    for q in range(2, qmax + 1):
        p = next(t for t in range(2, q + 1) if q % t == 0)
        x = q
        while x % p == 0: x //= p
        if x == 1: out.append(q)
    return out

ap = argparse.ArgumentParser()
ap.add_argument("d", type=int); ap.add_argument("D", type=int)
ap.add_argument("lo", type=int); ap.add_argument("hi", type=int); ap.add_argument("secs", type=int)
ap.add_argument("--seeds", type=int, default=2); ap.add_argument("--nmax", type=int, default=64)
ap.add_argument("--fam", default="sl,psl,pgl,tpgl,csl,prod"); ap.add_argument("--qmax", type=int, default=400)
ap.add_argument("--K", type=int, default=8); ap.add_argument("--seed0", type=int, default=1)
ap.add_argument("--best", type=float, default=1.0); ap.add_argument("--maxscore", type=float, default=None)
ap.add_argument("--show", action="store_true", help="print N, score and the job, for inspection")
a = ap.parse_args()
fams = set(a.fam.split(","))
bases = []   # (order, spec)
for q in prime_powers(a.qmax):
    o = q * (q * q - 1)
    if "sl" in fams and q % 2: bases.append((o, f"sl {q}"))          # SL = PSL for q even
    if "psl" in fams: bases.append((o // (2 if q % 2 else 1), f"psl {q}"))
    if "pgl" in fams and q % 2: bases.append((o, f"pgl {q}"))        # PGL = PSL for q even
    if "agl1" in fams: bases.append((q * (q - 1), f"agl1 {q}"))
    if "tpgl" in fams and q % 2: bases.append((o, f"tpgl {q}"))
    if "csl" in fams and q % 2: bases.append((o // 2, f"csl {q}"))      # order |PSL| * n, n even
if "prod" in fams:
    small = [(q * (q * q - 1) // (2 if q % 2 else 1), f"psl {q}") for q in prime_powers(64) if q >= 5]   # psl 4 = psl 5 = A5
    small += [(q * (q * q - 1), f"sl {q}") for q in prime_powers(32) if q % 2 and q >= 5]
    for i, (o1, s1) in enumerate(small):
        for o2, s2 in small[i:]:
            if s1 != s2 and o1 * o2 <= a.hi: bases.append((o1 * o2, f"prod {s1} {s2}"))
cands = set()
for o, spec in bases:
    if o > a.hi: continue
    for n in range(max(1, -(-a.lo // o)), a.hi // o + 1):
        if n <= a.nmax and not (spec.startswith("csl") and n % 2): cands.add((o * n, spec, n))
rated = []
for N, spec, n in sorted(cands):
    try:
        sc = score(a.d, group_counts(spec.split(), n))[0]
    except ValueError:
        sc = None
    rated.append((N, spec, n, sc))
if a.best < 1.0 or a.maxscore is not None:
    rated = [r for r in rated if r[3] is not None]
    if a.maxscore is not None:
        rated = [r for r in rated if r[3] <= a.maxscore]
    if a.best < 1.0 and rated:
        cut = sorted(r[3] for r in rated)[max(0, int(len(rated) * a.best) - 1)]
        rated = [r for r in rated if r[3] <= cut]
for N, spec, n, sc in rated:
    for s in range(a.seed0, a.seed0 + a.seeds):
        if a.show:
            print(N, "%.2e" % sc if sc is not None else "-", end=" | ")
        print(a.d, a.D, a.secs, s, a.K, spec, n)
