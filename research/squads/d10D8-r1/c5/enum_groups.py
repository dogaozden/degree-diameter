"""Enumerate haar_sym group specs Q x Z_n with LO <= |Q| * n <= HI (n <= NMAX), for the c5 card.
usage: python3 enum_groups.py LO HI NMAX > cands.tsv      lines: N <TAB> family-tag <TAB> spec for haar_sym
Atoms: sl/psl/pgl/agl1 q (prime powers q), heis q (q^3), meta m k r (Z_m x| Z_k, r^k = 1 mod m, r != 1; k in KS, m*k bounded).
Products of 2 atoms and of 3 atoms (nested prod as in parse_group). Specs are de-duplicated."""
import sys, math
import numpy as np
LO, HI, NMAX = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
KS = [3, 5, 4, 6, 7, 2]          # meta quotient orders tried (k=2 dihedral: included last, sanity only)
META_NMAX = 60                   # meta-factor atoms only with small n-products (they are solvable, screened as a sample)

def factor(n):
    f, p = {}, 2
    while p * p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1; n //= p
        p += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f
def is_pp(q): return q >= 2 and len(factor(q)) == 1

atoms = []   # (tokens, order, family)
for q in range(3, 1000):
    if not is_pp(q): continue
    o = q * (q * q - 1)
    if o <= HI:
        atoms.append((['sl', str(q)], o, 'sl'))
        atoms.append((['pgl', str(q)], o, 'pgl'))
    if q % 2 and o // 2 <= HI:
        atoms.append((['psl', str(q)], o // 2, 'psl'))
for q in range(2, 800):
    if is_pp(q) and q * (q - 1) <= HI:
        atoms.append((['agl1', str(q)], q * (q - 1), 'agl1'))
for q in range(2, 90):
    if is_pp(q) and q ** 3 <= HI:
        atoms.append((['heis', str(q)], q ** 3, 'heis'))

def roots_mod(m, k):
    """all r in [2, m) with r^k = 1 mod m and r != 1 (numpy, m <= ~1e6)."""
    x = np.arange(m, dtype=np.int64); acc = np.ones(m, dtype=np.int64); base = x.copy(); e = k
    while e:
        if e & 1: acc = acc * base % m
        base = base * base % m; e >>= 1
    idx = np.nonzero(acc == 1 % m)[0]
    return [int(r) for r in idx if r >= 2 and r != 1]
metas = []
for k in KS:
    # metacyclic Q = Z_m x| Z_k of order m*k; combined with n: m k n in [LO, HI]
    for n in range(1, META_NMAX + 1):
        mlo = -(-LO // (k * n)); mhi = HI // (k * n)
        for m in range(max(mlo, 3), mhi + 1):
            if k * m * n > HI: break
            rs = roots_mod(m, k)
            if not rs: continue
            # one representative r per (m,k): the one with the fewest fixed points gcd(r-1, m)
            r = min(rs, key=lambda r: (math.gcd(r - 1, m), r))
            metas.append((['meta', str(m), str(k), str(r)], m * k, 'meta-k%d' % k))
    # (k, n) loop above only produced n-values for this k; the Q-atoms for meta are returned as atoms below
for toks, o, tag in metas:
    atoms.append((toks, o, tag))

out = []
def add(toks, order, tag, nmax=NMAX):
    if order > HI: return
    nlo = max(1, -(-LO // order)); nhi = min(nmax, HI // order)
    for n in range(nlo, nhi + 1):
        out.append((order * n, tag, ' '.join(toks + [str(n)])))

for toks, o, tag in atoms:
    add(toks, o, tag)
A = sorted(atoms, key=lambda a: a[1])
for (t1, o1, g1) in A:
    for (t2, o2, g2) in A:
        if o1 * o2 > HI: break
        if o1 * o2 > HI: continue
        add(['prod'] + t1 + t2, o1 * o2, 'prod:%s*%s' % (g1, g2), NMAX)
for (t1, o1, g1) in A:
    for (t2, o2, g2) in A:
        if o1 * o2 > HI: break
        for (t3, o3, g3) in A:
            if o1 * o2 * o3 > HI: break
            if o3 < o2: continue
            add(['prod', 'prod'] + t1 + t2 + t3, o1 * o2 * o3, 'prod3:%s*%s*%s' % (g1, g2, g3), NMAX)
seen = set()
for N, tag, spec in sorted(out):
    if spec in seen: continue
    seen.add(spec)
    print('%d\t%s\t%s' % (N, tag, spec))
