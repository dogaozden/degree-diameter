#!/usr/bin/env python3
"""Search Cayley digraphs Cay(G, S) on groups of order m = C(k,2) satisfying Theorem Q's A-conditions:
|S| = k-2, S cap S^-1 = {}, and for g != e: #{(s,t) in S^2 : s t^-1 = g} = 0 if g in S u S^-1, else 2
(common out-neighbours of x and gx...). Groups: cyclic Z_m, and for m = 55 also Z_11 x| Z_5.
Each solution A is then checked for a signing (signs_gf2)."""
import sys, itertools
import numpy as np
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153
from signs_gf2 import solve as signsolve

def groups(m):
    # elements as tuples, mult, inverse
    yield 'Z%d' % m, list(range(m)), (lambda a, b: (a + b) % m), (lambda a: (-a) % m), 0
    if m == 55:
        # Z_11 x| Z_5 with 5-th roots of unity mod 11: r = 3 (3^5 = 243 = 1 mod 11)
        r = 3
        els = [(a, b) for a in range(11) for b in range(5)]
        def mul(x, y):
            return ((x[0] + pow(r, x[1], 11) * y[0]) % 11, (x[1] + y[1]) % 5)
        def inv(x):
            b = (-x[1]) % 5
            return ((-pow(r, b, 11) * x[0]) % 11, b)
        yield 'Z11:Z5', els, mul, inv, (0, 0)

def search(k, maxsol=50):
    m = k * (k - 1) // 2; g = k - 2
    for name, els, mul, inv, e in groups(m):
        nonid = [x for x in els if x != e]
        pool = IDPool(); cl = []
        v = {x: pool.id(x) for x in nonid}
        cl += CardEnc.equals([v[x] for x in nonid], bound=g, vpool=pool, encoding=EncType.seqcounter).clauses
        for x in nonid:
            if inv(x) != x: cl.append([-v[x], -v[inv(x)]])
            else: cl.append([-v[x]])
        # out-neighbours of vertex a: {a s}; common out-neighbours of a and b=a h: s,t with a s = a h t -> s t^-1 = h
        for h in nonid:
            ys = []
            for t in nonid:
                s = mul(h, t)
                if s == e or s == t: continue
                y = pool.id(('y', h, t)); cl += [[-y, v[s]], [-y, v[t]], [y, -v[s], -v[t]]]; ys.append(y)
            adj = pool.id(('adj', h))
            hi = inv(h)
            cl += [[-adj, v[h], v[hi]], [adj, -v[h]], [adj, -v[hi]]]
            # adjacent -> 0, else exactly 2
            for y in ys: cl.append([-adj, -y])
            enc = CardEnc.equals(ys, bound=2, vpool=pool, encoding=EncType.seqcounter)
            act = adj
            for c in enc.clauses: cl.append(c + [act])
        s = Cadical153(bootstrap_with=cl)
        nsol = 0
        while s.solve() and nsol < maxsol:
            mdl = set(l for l in s.get_model() if l > 0)
            S = [x for x in nonid if v[x] in mdl]
            idx = {x: i for i, x in enumerate(els)}
            A = np.zeros((m, m), dtype=np.int64)
            for a in els:
                for t in S: A[idx[a], idx[mul(a, t)]] = 1
            M = 2 * np.eye(m, dtype=np.int64) + A
            ok1 = np.array_equal(M @ M.T, k * np.eye(m, dtype=np.int64) + 2) and np.array_equal(M.T @ M, k * np.eye(m, dtype=np.int64) + 2)
            sg = signsolve(A)[0] if ok1 else None
            print(name, 'S =', S, 'A-conditions', ok1, 'signing', sg, flush=True)
            if sg: np.save(f'A_k{k}_{name}_signable.npy', A)
            nsol += 1
            s.add_clause([-v[x] for x in S])
        print(name, 'solutions found:', nsol, flush=True)

if __name__ == '__main__':
    search(int(sys.argv[1]))
