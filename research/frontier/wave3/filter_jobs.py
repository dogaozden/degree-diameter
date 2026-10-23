"""Drop job lines whose group order N is <= a bound (e.g. after a new record), keeping the order of the rest.

  python3 wave3/filter_jobs.py JOBFILE MIN_N_EXCLUSIVE > NEWFILE
Orders: sl/pgl q -> q(q^2-1), psl q -> q(q^2-1)/gcd(2,q-1), agl1 q -> q(q-1), meta m k r -> m k, cyc -> 1,
tpgl q -> q(q^2-1), csl q -> q(q^2-1)/2, prod A B -> |A||B|; times the cyclic factor n (last token).
"""
import math
import sys


def order(tok, i=0):
    t = tok[i]
    if t in ("sl", "pgl", "tpgl"):
        q = int(tok[i + 1]); j = i + 2
        if j < len(tok) and tok[j] == "poly": j += 2
        return q * (q * q - 1), j
    if t in ("psl", "csl"):
        q = int(tok[i + 1]); j = i + 2
        if j < len(tok) and tok[j] == "poly": j += 2
        return q * (q * q - 1) // math.gcd(2, q - 1), j
    if t == "agl1":
        q = int(tok[i + 1]); j = i + 2
        if j < len(tok) and tok[j] == "poly": j += 2
        return q * (q - 1), j
    if t == "meta":
        return int(tok[i + 1]) * int(tok[i + 2]), i + 4
    if t == "cyc":
        return 1, i + 1
    if t == "prod":
        a, j = order(tok, i + 1)
        b, j = order(tok, j)
        return a * b, j
    raise ValueError(t)


bound = int(sys.argv[2])
for ln in open(sys.argv[1]):
    t = ln.split()
    if not t or t[0].startswith("#"):
        print(ln, end="")
        continue
    grp = t[5:-1]
    o, j = order(grp)
    if o * int(t[-1]) > bound:
        print(ln, end="")
