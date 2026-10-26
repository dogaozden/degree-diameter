# Enumerate abc groups M x| Z_k (M = sum of F_{p^f}, component p:d acts by a primitive d-th root, d >= 3, p not | d),
# order in [1094, 1350], at least one characteristic-2 component with f >= 2. Prints "order k comps".
from itertools import combinations_with_replacement
from math import gcd

def isprime(n):
    return n > 1 and all(n % q for q in range(2, int(n ** 0.5) + 1))

def ordmod(p, d):
    x, o = p % d, 1
    while x != 1:
        x = x * p % d
        o += 1
    return o

LO, HI = 1094, 1350
primes = [p for p in range(2, HI) if isprime(p)]
out = []
for k in range(3, HI // 2 + 1):
    divs = [d for d in range(3, k + 1) if k % d == 0]
    cands = []
    for d in divs:
        for p in primes:
            if d % p == 0:
                continue
            f = ordmod(p, d)
            if p ** f * k > HI:
                continue
            cands.append((p, d, f))
    # multisets of 1..3 components
    for r in (1, 2, 3):
        for combo in combinations_with_replacement(range(len(cands)), r):
            comps = [cands[i] for i in combo]
            if not any(p == 2 and f >= 2 for p, d, f in comps):
                continue
            M = 1
            for p, d, f in comps:
                M *= p ** f
            order = k * M
            if LO <= order <= HI:
                spec = ",".join(f"{p}:{d}" for p, d, f in comps)
                out.append((order, k, spec))
out.sort()
for order, k, spec in out:
    print(order, k, spec)
print(len(out), "groups")
