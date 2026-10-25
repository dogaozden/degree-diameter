#!/usr/bin/env python3
"""List the cubes (assignments of arcs x->z, x in the first `rows` vertices of O, z in I) that survive unit
propagation, for planning a cube-and-conquer run. usage: cube_list.py k rows out.json [enc options]"""
import sys, itertools, json, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pysat.solvers import Cadical153
from enc_quot import build
k = int(sys.argv[1]); rows = int(sys.argv[2]); out = sys.argv[3]; opts = sys.argv[4:]
g = k - 2
cnf, pool, a = build(k, signs='--signs' in opts, sym='--sym' in opts, nf2='--nf2' in opts, ntt='--ntt' in opts,
                     alltr='--alltr' in opts)
O = list(range(1, g + 1)); I = list(range(g + 1, 2 * g + 1))
cv = [a[x, z] for x in O[:rows] for z in I]
s = Cadical153(bootstrap_with=cnf.clauses)
surv = []; refuted = []
# tree search with propagation pruning (avoids enumerating all 2^(rows*g) leaves)
def rec(pre):
    ok, _ = s.propagate(assumptions=pre)
    if not ok: refuted.append(list(pre)); return
    if len(pre) == len(cv): surv.append(list(pre)); return
    v = cv[len(pre)]
    rec(pre + [-v]); rec(pre + [v])
rec([])
json.dump({'k': k, 'rows': rows, 'opts': opts, 'cube_vars': cv, 'surviving': surv, 'refuted': refuted}, open(out, 'w'))
print(f'k={k} rows={rows}: {len(surv)} surviving cubes, {len(refuted)} refuted tree nodes')
