import sys
LO, HI = 262081, 264500
def isprime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True
primes = [p for p in range(3, 2000) if isprime(p)]
F = []
for p in primes:
    if p * 3 > HI: break
    for k in range(3, p):
        if (p - 1) % k: continue
        if p * k > HI: break
        if p * k < 12: continue
        F.append((f"F({p},{k})", p * k, ("meta", p, k)))
# keep only Frobenius-type atoms plus small ones
small = [("Z7x|Z3", 21, ("meta", 7, 3)), ("A4", 12, None), ("SL25", 120, None), ("PSL27", 168, None), ("SL27", 336, None)]
atoms = [a for a in F] + [("PSL(%d)" % q, q*(q*q-1)//2, None) for q in primes if q*(q*q-1)//2 <= HI and q>3]
atoms += [("SL(%d)" % q, q*(q*q-1), None) for q in primes if q*(q*q-1) <= HI and q > 2]
atoms += [("AGL1(%d)" % q, q*(q-1), None) for q in primes if q*(q-1) <= HI and q > 3]
atoms += small
atoms = [a for a in atoms if a[1] <= HI]
atoms.sort(key=lambda x: x[1])
pairs = []
for i in range(len(atoms)):
    for j in range(i, len(atoms)):
        o = atoms[i][1] * atoms[j][1]
        if o > HI: break
        for n in range(1, HI // o + 1):
            N = o * n
            if LO <= N <= HI:
                pairs.append((N, atoms[i][0], atoms[j][0], n))
print(len(pairs))
# prefer both-Frobenius-type with odd coprime orders and the (Z7x|Z3) x F family
def odd(x): return x % 2 == 1
from math import gcd
out = []
for N, a, b, n in pairs:
    oa = [x for x in atoms if x[0] == a][0][1]; ob = [x for x in atoms if x[0] == b][0][1]
    if a.startswith("F") and b.startswith("F") and gcd(oa, ob) == 1 and odd(oa*ob*n):
        out.append((N, a, b, n))
    if a == "Z7x|Z3" and (b.startswith("F")):
        out.append((N, a, b, n))
print("filtered", len(out))
for o in sorted(out)[:300]: print(*o)
