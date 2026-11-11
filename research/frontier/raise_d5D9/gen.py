# Candidate groups for Haar (5,9) with |G| in (LO, HI]; writes "order spec n" lines.
import math, collections, sys
LO, HI = 14280, 15186
MAXN = int(sys.argv[1]) if len(sys.argv) > 1 else 60
MAXK = 60
def prime_power(q):
    for p in range(2, q + 1):
        if all(p % d for d in range(2, int(p ** 0.5) + 1)):
            x, k = q, 0
            while x % p == 0: x //= p; k += 1
            return (p, k) if x == 1 else None
    return None
out = []
for q in range(5, 200):
    if prime_power(q) is None: continue
    o = q * (q * q - 1)
    fam = []
    if q % 2:
        fam.append((o // 2, f"psl {q}")); fam.append((o, f"pgl {q}"))
    fam.append((o, f"sl {q}"))
    for order, spec in fam:
        for n in range(1, MAXN + 1):
            if LO < order * n <= HI: out.append((order * n, spec, n))
per = collections.Counter()
for m in range(2, HI + 1):
    for k in range(2, min(MAXK, HI // m) + 1):
        if m * k <= LO or m * k > HI: continue
        cnt = 0
        for r in range(2, m):
            if math.gcd(r, m) != 1 or pow(r, k, m) != 1: continue
            if any(pow(r, j, m) == 1 for j in range(1, k)): continue      # order of r is exactly k
            out.append((m * k, f"meta {m} {k} {r}", 1)); cnt += 1
            if cnt == 2: break
out.sort()
with open('cands.txt', 'w') as f:
    for o, s, n in out: f.write(f"{o} {s} {n}\n")
c = collections.Counter(s.split()[0] for _, s, _ in out)
print(len(out), dict(c))
