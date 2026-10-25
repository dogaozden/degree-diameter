#!/usr/bin/env python3
"""Sub-case of the A-only instance: at vertex 0, every x in O has exactly r out-neighbours in I and every z in I has
exactly r in-neighbours in O (B is r-regular). A SAT answer is an oriented graph A (then check the signing);
UNSAT only excludes this sub-case. No lex-leader (the sub-case constraint is symmetric, but we keep it simple).
usage: subcase.py k r out.cnf"""
import sys
from pysat.card import CardEnc, EncType
from enc_quot import build

k = int(sys.argv[1]); r = int(sys.argv[2]); g = k - 2
cnf, pool, a = build(k, sym=True, nf2=True, ntt=True, alltr=True)
O = list(range(1, g + 1)); I = list(range(g + 1, 2 * g + 1))
for x in O:
    cnf.extend(CardEnc.equals([a[x, z] for z in I], bound=r, vpool=pool, encoding=EncType.seqcounter).clauses)
for z in I:
    cnf.extend(CardEnc.equals([a[x, z] for x in O], bound=r, vpool=pool, encoding=EncType.seqcounter).clauses)
cnf.to_file(sys.argv[3])
with open(sys.argv[3] + '.map', 'w') as f:
    import json
    json.dump({'k': k, 'a': [[c, d, v] for (c, d), v in a.items()]}, f)
print(f'k={k} r={r} vars={cnf.nv} clauses={len(cnf.clauses)}')
