#!/usr/bin/env python3
"""Search A (Theorem Q conditions) invariant under a semiregular cyclic automorphism of prime order p dividing m:
vertices (r, x), r < m/p orbits, x in Z_p; arc (r,x) -> (s,x+d) for all x iff variable v[r][s][d].
Solutions are expanded, re-checked with numpy (M M^T = M^T M = kI + 2J) and the signing is decided by GF(2).
usage: semireg_search.py k p [maxsol]"""
import sys, itertools
import numpy as np
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153
from signs_gf2 import solve as signsolve

k = int(sys.argv[1]); p = int(sys.argv[2]); maxsol = int(sys.argv[3]) if len(sys.argv) > 3 else 20
m = k * (k - 1) // 2; g = k - 2; assert m % p == 0; q = m // p
pool = IDPool(); cl = []
v = {}
for r in range(q):
    for s in range(q):
        for d in range(p):
            if r == s and d == 0: continue
            v[r, s, d] = pool.id(('v', r, s, d))
for r in range(q):  # out-degree g
    cl += CardEnc.equals([v[r, s, d] for s in range(q) for d in range(p) if (r, s, d) in v], bound=g, vpool=pool,
                         encoding=EncType.seqcounter).clauses
    cl += CardEnc.equals([v[s, r, d] for s in range(q) for d in range(p) if (s, r, d) in v], bound=g, vpool=pool,
                         encoding=EncType.seqcounter).clauses
for (r, s, d), x in v.items():  # oriented
    y = v.get((s, r, (-d) % p))
    if y is not None and (r, s, d) < (s, r, (-d) % p): cl.append([-x, -y])
    if r == s and (2 * d) % p == 0: cl.append([-x])
def arc(r, x, s, y):
    d = (y - x) % p
    return v.get((r, s, d))
# pair conditions for vertex (r,0) and (s,d), (r,0) != (s,d)
for r in range(q):
    for s in range(q):
        for d in range(p):
            if r == s and d == 0: continue
            if (s, r, (-d) % p) < (r, s, d) and False: pass
            adj = pool.id(('adj', r, s, d))
            a1 = arc(r, 0, s, d); a2 = arc(s, d, r, 0)
            cl += [[-adj, a1, a2], [adj, -a1], [adj, -a2]]
            for direction in ('out', 'in'):
                ys = []
                for t in range(q):
                    for e in range(p):
                        if (t, e) in ((r, 0), (s, d)): continue
                        if direction == 'out': u1, u2 = arc(r, 0, t, e), arc(s, d, t, e)
                        else: u1, u2 = arc(t, e, r, 0), arc(t, e, s, d)
                        yv = pool.id(); cl += [[-yv, u1], [-yv, u2], [yv, -u1, -u2]]; ys.append(yv)
                for yv in ys: cl.append([-adj, -yv])
                for c in CardEnc.equals(ys, bound=2, vpool=pool, encoding=EncType.seqcounter).clauses:
                    cl.append(c + [adj])
s = Cadical153(bootstrap_with=cl)
nsol = 0
while nsol < maxsol and s.solve():
    mdl = set(l for l in s.get_model() if l > 0)
    A = np.zeros((m, m), dtype=np.int64)
    for (r, s_, d), x in v.items():
        if x in mdl:
            for xx in range(p): A[r * p + xx, s_ * p + (xx + d) % p] = 1
    M = 2 * np.eye(m, dtype=np.int64) + A
    ok = np.array_equal(M @ M.T, k * np.eye(m, dtype=np.int64) + 2) and np.array_equal(M.T @ M, k * np.eye(m, dtype=np.int64) + 2)
    sg = signsolve(A)[0] if ok else None
    nsol += 1
    print(f'solution {nsol}: A-conditions {ok}, signing {sg}', flush=True)
    if sg: np.save(f'A_k{k}_p{p}_signable.npy', A)
    s.add_clause([-x for x in v.values() if x in mdl])
print(f'k={k} p={p}: {nsol} solutions (cap {maxsol})')
