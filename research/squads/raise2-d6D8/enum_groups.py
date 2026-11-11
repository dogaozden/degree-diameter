"""Enumerate candidate groups G with LO <= |G| <= HI for the (6,8) raise, round 2.
Families (all accepted by research/structured/haar_sym.c with ORBIT set):
  sl/psl/pgl q x Z_n (any n <= NMAX), agl1 q x Z_n, meta m k r (Z_m x|_r Z_k, k <= KMAX, r of order d>1 with d | k),
  heis q x Z_n.  Prints one spec per line: N  <tokens for haar_sym>.
usage: python3 enum_groups.py LO HI [NMAX] [KMAX]
"""
import sys
from math import gcd

def factor(n):
    f, p = {}, 2
    while p * p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def is_pp(q):
    return q > 1 and len(factor(q)) == 1

def order_mod(r, m):
    x, o = r % m, 1
    while x != 1 % m:
        x = x * r % m
        o += 1
    return o

LO, HI = int(sys.argv[1]), int(sys.argv[2])
NMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 400
KMAX = int(sys.argv[4]) if len(sys.argv) > 4 else 60
out = []
# base groups: (token string, order of base group)
base = []
for q in range(3, 200):
    if not is_pp(q):
        continue
    o = q * (q * q - 1)
    if o <= HI:
        base.append(('sl %d' % q, o))
        base.append(('pgl %d' % q, o))
        if q % 2 and o // 2 <= HI:
            base.append(('psl %d' % q, o // 2))
for q in range(2, 200):
    if is_pp(q) and q * (q - 1) <= HI:
        base.append(('agl1 %d' % q, q * (q - 1)))
for q in range(3, 40):
    if is_pp(q) and q ** 3 <= HI:
        base.append(('heis %d' % q, q ** 3))
seen = set()
for s, o in base:
    for n in range(1, NMAX + 1):
        N = o * n
        if N < LO:
            continue
        if N > HI:
            break
        spec = '%s %d' % (s, n)
        if (N, spec) not in seen:
            seen.add((N, spec))
            out.append((N, spec))
# metacyclic Z_m x|_r Z_k : r of order d > 1, d | k, gcd(r,m)=1; keep the two smallest r per (m, k, d)
for k in range(2, KMAX + 1):
    mlo, mhi = -(-LO // k), HI // k
    for m in range(max(mlo, 3), mhi + 1):
        if (m * k) < LO:
            continue
        found = {}
        for r in range(2, m):
            if pow(r, k, m) != 1 % m or gcd(r, m) != 1:
                continue
            d = order_mod(r, m)
            if d <= 1 or k % d:
                continue
            found.setdefault(d, [])
            if len(found[d]) < 2:
                found[d].append(r)
        for d, rs in found.items():
            for r in rs:
                spec = 'meta %d %d %d' % (m, k, r)
                if (m * k, spec) not in seen:
                    seen.add((m * k, spec))
                    out.append((m * k, spec))
for N, spec in sorted(out):
    print(N, spec)
