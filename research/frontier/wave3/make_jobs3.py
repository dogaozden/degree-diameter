"""Job lists for haar_gen3 (wave 3): all group families with order N = |M| * n in [lo, hi].

  python3 make_jobs3.py d D lo hi seconds [--seeds S] [--nmax NMAX] [--fam sl,psl,pgl,prod,agl1,meta] [--qmax Q]
Families M: sl/psl/pgl(2,q), q a prime or prime power; prod of two PSL/SL(2,q) (small q); agl1 q.
Each line is batch.sh format: d D seconds seed K group... n, sorted by N (smallest first).
Run with:  BIN=./haar_gen3 bash batch.sh JOBFILE
"""
import argparse

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
ap.add_argument("--fam", default="sl,psl,pgl,prod"); ap.add_argument("--qmax", type=int, default=400)
ap.add_argument("--K", type=int, default=8); ap.add_argument("--seed0", type=int, default=1)
a = ap.parse_args()
fams = set(a.fam.split(","))
bases = []   # (order, spec)
for q in prime_powers(a.qmax):
    o = q * (q * q - 1)
    if "sl" in fams and q % 2: bases.append((o, f"sl {q}"))          # SL = PSL for q even
    if "psl" in fams: bases.append((o // (2 if q % 2 else 1), f"psl {q}"))
    if "pgl" in fams and q % 2: bases.append((o, f"pgl {q}"))        # PGL = PSL for q even
    if "agl1" in fams: bases.append((q * (q - 1), f"agl1 {q}"))
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
        if n <= a.nmax: cands.add((o * n, spec, n))
for N, spec, n in sorted(cands):
    for s in range(a.seed0, a.seed0 + a.seeds):
        print(a.d, a.D, a.secs, s, a.K, spec, n)
