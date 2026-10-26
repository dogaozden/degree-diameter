"""a04: enumerate split abelian-by-cyclic groups M x| Z_k with order N in [LO, HI] whose components may have d = 1
(central) or d = 2 (inversion), with at least one d >= 3; faithful (lcm of the d's = k).
Component (p, d, e): F_{p^f} with f = ord_d(p) (f = 1 for d <= 2), generator acts by w^e.
Usage: python3 enum.py LO HI  -> lines "N k spec" with spec "p:d[@e],..." (abc.py build format)."""
import sys, importlib.util
from math import lcm
from itertools import combinations_with_replacement
spec = importlib.util.spec_from_file_location("abcmod", "/home/user/degree-diameter/research/squads/b48/tools/abc.py")
A = importlib.util.module_from_spec(spec); spec.loader.exec_module(A)
LO, HI = int(sys.argv[1]), int(sys.argv[2])
primes = [p for p in range(2, HI) if A.is_prime(p)]
out = set()
for k in range(3, HI + 1):
    cands = []   # (size p^f, p, d)
    for d in A.divisors(k):
        for p in primes:
            if d == 1:
                cands.append((p, p, 1, 1))
                continue
            if d % p == 0 or (d == 2 and p == 2):
                continue
            f = A.ordmod(p, d)
            if p ** f <= HI // k:
                cands.append((p ** f, p, d, f))
    cands = sorted(set(cands))
    def rec(start, prod, chosen):
        if chosen:
            ds = [c[2] for c in chosen]
            if LO <= k * prod <= HI and any(d >= 3 for d in ds) and lcm(*ds) == k:
                ncomp = len(chosen)
                if ncomp <= 4:
                    s = ",".join(f"{c[1]}:{c[2]}" for c in chosen)
                    out.add((k * prod, k, s))
        if len(chosen) >= 4:
            return
        for i in range(start, len(cands)):
            q = cands[i][0]
            if prod * q * k > HI:
                break
            rec(i, prod * q, chosen + [cands[i]])
    rec(0, 1, [])
for N, k, s in sorted(out):
    print(N, k, s)
