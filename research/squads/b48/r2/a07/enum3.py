# Enumerate three-component abc groups G = (F_{p1^f1} + F_{p2^f2} + F_{p3^f3}) x| Z_k, d_i >= 3, d_i | k,
# order M*k in [LO, HI]. Component "p:d" acts by a primitive d-th root w; "p:d@e" by w^e.
# A single component of a (p,d) class is normalised to e=1; repeated (p,d) components take e in units mod d.
import sys
from math import gcd
LO, HI = int(sys.argv[1]), int(sys.argv[2])

def is_prime(n):
    return n >= 2 and all(n % q for q in range(2, int(n ** 0.5) + 1))

def ordmod(p, d):
    x, o = p % d, 1
    while x != 1:
        x = x * p % d
        o += 1
    return o

primes = [p for p in range(2, HI) if is_prime(p)]
out = []
for k in range(3, HI + 1):
    cands = []
    for d in range(3, k + 1):
        if k % d:
            continue
        for p in primes:
            if d % p == 0:
                continue
            f = ordmod(p, d)
            size = p ** f
            if size * 4 > HI // k + 0 and size > HI // k:
                continue
            cands.append((size, p, d))
    cands.sort()
    for i in range(len(cands)):
        for j in range(i, len(cands)):
            for l in range(j, len(cands)):
                c = [cands[i], cands[j], cands[l]]
                M = c[0][0] * c[1][0] * c[2][0]
                N = M * k
                if not (LO <= N <= HI):
                    continue
                def rec(idx, cur):
                    if idx == 3:
                        out.append((k, cur, N))
                        return
                    _, p, d = c[idx]
                    prev = [t for t in range(idx) if c[t][1] == p and c[t][2] == d]
                    if not prev:
                        rec(idx + 1, cur + [f"{p}:{d}"])
                    else:
                        for e in range(1, d):
                            if gcd(e, d) == 1:
                                rec(idx + 1, cur + [f"{p}:{d}" + (f"@{e}" if e != 1 else "")])
                rec(0, [])
for k, comps, N in out:
    print(k, ",".join(comps), N)
