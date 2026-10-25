#!/usr/bin/env python3
"""Split the k = 11 A-only instance by M = the largest number of directed triangles on an arc.
Rule: relabel so that the arc 0 -> 1 lies on the most directed triangles (M of them); vertex 1 is then in O.
Cube M: every arc u -> x lies on at most M directed triangles u -> x -> z -> u, and the arc 0 -> 1 lies on exactly M
(= exactly M arcs from vertex 1 into I). Lex-leader: all transpositions of I, and transpositions of O that fix vertex 1
(both preserve the rule). Cubes M = 0..9 cover every solution (M <= 9 = out-degree).
usage: tausplit.py M out.cnf"""
import sys, itertools
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from enc_quot import build
M = int(sys.argv[1]); out = sys.argv[2]
k = 11; g = k - 2; m = k * (k - 1) // 2
O = list(range(1, g + 1)); I = list(range(g + 1, 2 * g + 1))
op = [(u, v) for u, v in itertools.combinations(O, 2) if 1 not in (u, v)]
ip = list(itertools.combinations(I, 2))
cnf, pool, a = build(k, sym=True, nf2=True, ntt=True, alltr=True, opairs=op, ipairs=ip)
tri = {}
def T(p, q, r):
    key = min((p, q, r), (q, r, p), (r, p, q))
    if key not in tri:
        v = pool.id(); tri[key] = v; x, y, z = key
        cnf.extend([[-v, a[x, y]], [-v, a[y, z]], [-v, a[z, x]], [v, -a[x, y], -a[y, z], -a[z, x]]])
    return tri[key]
for u in range(m):
    for x in range(m):
        if u == x: continue
        lits = [T(u, x, z) for z in range(m) if z not in (u, x)]
        if M == 0:
            for l in lits: cnf.append([-l])
        else:
            cnf.extend(CardEnc.atmost(lits, bound=M, vpool=pool, encoding=EncType.seqcounter).clauses)
cnf.extend(CardEnc.equals([a[1, z] for z in I], bound=M, vpool=pool, encoding=EncType.seqcounter).clauses)
cnf.to_file(out); print(f'M={M}: vars={cnf.nv} clauses={len(cnf.clauses)}')
