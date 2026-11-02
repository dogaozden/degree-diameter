import math
LO, HI = 6209, 6450
def isprime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True
def order_mod(r, m):
    x, o = r % m, 1
    while x != 1 % m:
        x = x * r % m; o += 1
    return o
cands = {}
for k in range(8, 400):
    for m in range(max(3, -(-LO // k)), HI // k + 1):
        N = m * k
        if N < LO or N > HI: continue
        seen = set()
        for r in range(2, m):
            if math.gcd(r, m) != 1: continue
            if pow(r, k, m) != 1 % m: continue
            o = order_mod(r, m)
            if o == k and isprime(m): continue          # Frobenius: excluded (e01/e02)
            sub = frozenset(pow(r, j, m) for j in range(o))
            if sub in seen: continue
            seen.add(sub)
            cands.setdefault((N, m, k, r), o)
print(len(cands), "candidate (m,k,r) classes", file=__import__('sys').stderr)
rows = []
for (N, m, k, r), o in cands.items():
    pref = 0
    if isprime(m): pref += 2
    if k & (k - 1) == 0: pref += 2
    if o == k // 2: pref += 2
    if 97 <= m <= 200: pref += 1
    rows.append((-pref, N, m, k, r, o))
rows.sort()
import sys
for row in rows:
    print(f"{-row[0]} N={row[1]} m={row[2]} k={row[3]} r={row[4]} ord={row[5]} prime_m={isprime(row[2])}")
