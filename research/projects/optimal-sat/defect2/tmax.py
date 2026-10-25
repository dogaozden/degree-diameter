#!/usr/bin/env python3
"""Split by the maximum number of directed triangles through a vertex.
  tmax.py le T out.cnf   : A-only instance (enc_quot --sym --nf2 --ntt --alltr) + "every vertex lies on at most T
                           directed triangles"
  tmax.py ge T out.cnf   : A-only instance + "vertex 0 lies on at least T directed triangles" (= at least T arcs
                           from O to I). Valid as a cube if vertex 0 is chosen with the maximum number of triangles,
                           which is compatible with the normal form and the lex-leader (they relabel only O, I, R).
The two cubes (le T-1, ge T) cover every solution: either all vertices have < T triangles, or the vertex with the
most triangles (relabelled as vertex 0) has >= T."""
import sys, itertools
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from enc_quot import build
mode, T, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
k = 11; g = k - 2; m = k * (k - 1) // 2
cnf, pool, a = build(k, sym=True, nf2=True, ntt=True, alltr=True)
O = list(range(1, g + 1)); I = list(range(g + 1, 2 * g + 1))
if mode == 'ge':
    cnf.extend(CardEnc.atleast([a[x, z] for x in O for z in I], bound=T, vpool=pool, encoding=EncType.totalizer).clauses)
else:
    tri = {}
    for p, q, r in itertools.permutations(range(m), 3):
        key = min((p, q, r), (q, r, p), (r, p, q))
        if key in tri: continue
        v = pool.id(); tri[key] = v
        x, y, z = key
        cnf.extend([[-v, a[x, y]], [-v, a[y, z]], [-v, a[z, x]], [v, -a[x, y], -a[y, z], -a[z, x]]])
    for v in range(m):
        lits = [tri[min((v, x, z), (x, z, v), (z, v, x))] for x in range(m) for z in range(m) if len({v, x, z}) == 3]
        lits = sorted(set(lits))
        if T == 0:
            for l in lits: cnf.append([-l])
        else:
            cnf.extend(CardEnc.atmost(lits, bound=T, vpool=pool, encoding=EncType.seqcounter).clauses)
cnf.to_file(out); print(f'{mode} {T}: vars={cnf.nv} clauses={len(cnf.clauses)}')
