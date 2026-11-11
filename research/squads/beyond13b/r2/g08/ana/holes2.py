#!/usr/bin/env python3
"""Classify holes of a haar_big0 EVAL (SL(2,p) x Z_n, ORBIT k=3) in the ORBIT (alpha-symmetric) frame.

usage: holes2.py EVALFILE p n [ORBFILE]
ORBFILE: the .best.orb state of an f = 0 run (its first generator s0 = S[0]); EVAL normalises S to T = S s0^-1,
so untagged (side A) holes of T are conjugates of the S-frame holes: H_T = s0 H_S s0^-1; tagged holes (second kind,
H(G,S^-1)) are unchanged. With ORBFILE absent, s0 = e (f >= 1 states, whose S contains e).
Group element (M, z), M in SL(2,p), z in Z_n.  alpha(M,z) = (g M g^-1, r z), g = [[0,-1],[1,-1]], r of order 3 mod n.
"""
import sys, re, math
from collections import Counter

def load_eval(fn):
    out = []
    for line in open(fn):
        m = re.match(r"uncovered (\d+) mat\((-?\d+),(-?\d+),(-?\d+),(-?\d+)\) z=(-?\d+)( \(B side\))?", line.strip())
        if m:
            M = tuple(int(m.group(i)) for i in range(2, 6))
            out.append((M, int(m.group(6)), 'T' if m.group(7) else 'U'))   # U = untagged (first kind), T = tagged (second kind)
    return out

def load_s0(fn):
    for line in open(fn):
        m = re.match(r"\s*\d+ mat\((-?\d+),(-?\d+),(-?\d+),(-?\d+)\) z=(-?\d+)", line)
        if m:
            return tuple(int(m.group(i)) for i in range(1, 5)), int(m.group(5))
    return None

def mmul(x, y, p):
    a, b, c, d = x; e, f, g, h = y
    return ((a*e + b*g) % p, (a*f + b*h) % p, (c*e + d*g) % p, (c*f + d*h) % p)

def minv(x, p):
    a, b, c, d = x
    return (d % p, (-b) % p, (-c) % p, a % p)

def morder(x, p):
    I = (1, 0, 0, 1); y = x; k = 1
    while y != I:
        y = mmul(y, x, p); k += 1
        if k > 4 * p + 10: return -1
    return k

def main(fn, p, n, orbfile=None):
    H = load_eval(fn)
    g = (0, p - 1, 1, p - 1); gi = minv(g, p)
    best = None
    for r in range(2, max(n, 3)):
        if n > 1 and math.gcd(r, n) == 1 and pow(r, 3, n) == 1 % n:
            fx = math.gcd(r - 1, n)
            if best is None or fx < best[1]: best = (r, fx)
    AR = best[0] if (best and n > 1) else 1
    s0 = ((1, 0, 0, 1), 0)
    if orbfile:
        s0 = load_s0(orbfile)
    M0, z0 = s0
    M0i = minv(M0, p)
    # S-frame: untagged (A-side first kind) holes H_S = s0^-1 H_T s0 (z unchanged); tagged unchanged
    rows = []
    for M, z, k in H:
        if k == 'U' and M0 != (1, 0, 0, 1):
            M2 = mmul(mmul(M0i, M, p), M0, p)
        else:
            M2 = M
        rows.append(dict(M=M2, z=z, kind=k, Mt=M))
    def alpha(M, z):
        return (mmul(mmul(g, M, p), gi, p), (AR * z) % n if n > 1 else 0)
    def inv(M, z):
        return (minv(M, p), (-z) % n if n > 1 else 0)
    print(f"# file {fn}\n# p={p} n={n} r={AR} (fixed z: {math.gcd(AR-1, n) if n>1 else 1}); s0={s0}; holes={len(rows)}")
    for kind, name in (('U', 'first kind (untagged)'), ('T', 'second kind (tagged)')):
        S = {(q['M'], q['z']) for q in rows if q['kind'] == kind}
        if not S: print(f"# {name}: 0 holes"); continue
        na = sum(1 for (M, z) in S if alpha(M, z) in S)
        ni = sum(1 for (M, z) in S if inv(M, z) in S)
        print(f"# {name}: {len(S)} holes; alpha-closed {na}/{len(S)}; inverse-closed {ni}/{len(S)}")
    print("# S-frame holes: kind | M | z | tr | ordM | ordG | central | commutes-with-g | alpha-fixed | inverse among holes")
    allS = {(q['M'], q['z'], q['kind']) for q in rows}
    cnt = Counter()
    for q in rows:
        M, z, kind = q['M'], q['z'], q['kind']
        tr = (M[0] + M[3]) % p
        cen = M[1] == 0 and M[2] == 0 and M[0] == M[3]
        ordM = morder(M, p)
        ordn = (n // math.gcd(z, n)) if n > 1 else 1
        ordG = ordM * ordn // math.gcd(ordM, ordn)
        cg = mmul(M, g, p) == mmul(g, M, p)
        afix = cg and ((AR * z - z) % n == 0 if n > 1 else True)
        iv = inv(M, z)
        ivin = any((a, b) == iv for (a, b, _) in allS)
        sg = ('+I' if M[0] == 1 else '-I') if cen else ''
        cnt[(kind, 'central' if cen else 'noncentral', sg, 'z=0' if z == 0 else 'z!=0')] += 1
        print(f"{kind} {str(M):22s} z={z:<4d} tr={tr:<4d} ordM={ordM:<5d} ordG={ordG:<6d} {sg:3s} cg={int(cg)} afix={int(afix)} invin={int(ivin)}")
    print("# counts (kind, central?, sign, z):")
    for k2, v in sorted(cnt.items()): print("#  ", k2, v)
    print("# traces:", sorted(Counter((q['kind'], (q['M'][0] + q['M'][3]) % p) for q in rows).items()))
    print("# orders G:", sorted(Counter(((q['kind']), morder(q['M'], p)) for q in rows).items()))
    zz = sorted({(q['kind'], q['z']) for q in rows})
    print("# z values (kind, z):", zz)
    print("# n-orbit of z under <r,-1>, classes:")
    if n > 1:
        cls = {}
        for z in range(1, n):
            if z in cls: continue
            o = set(); w = z
            for _ in range(3):
                o.add(w); o.add((-w) % n); w = (AR * w) % n
            for s in o: cls[s] = min(o)
        print("#   ", sorted(Counter((q['kind'], cls.get(q['z'], 0)) for q in rows if q['z'] != 0).items()))
        print("#    class sets:", sorted({tuple(sorted(set(v for v in range(1, n) if cls.get(v) == c))) for c in set(cls.values())}, key=lambda t: t[0])[:10])

if __name__ == '__main__':
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4] if len(sys.argv) > 4 else None)
