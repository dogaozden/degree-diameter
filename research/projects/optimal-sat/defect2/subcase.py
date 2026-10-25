#!/usr/bin/env python3
"""Sub-case of the A-only instance: at vertex 0, every x in O has exactly r out-neighbours in I and every z in I has
exactly r in-neighbours in O (B is r-regular). A SAT answer is an oriented graph A (then check the signing);
UNSAT only excludes this sub-case. Uses the same lex-leader clauses as enc_quot.py --sym --nf2 --alltr; that is sound
because both sub-case constraints are invariant under relabelling O and I.
usage: subcase.py k r out.cnf        (B r-regular)
       subcase.py k t:T out.cnf      (B has exactly T arcs, i.e. T directed triangles through vertex 0)
       subcase.py k row:r out.cnf    (every row of B has r ones; columns free)
       subcase.py k ab:5,5,4,4,4,4,4,3,3/5,5,4,4,4,4,4,3,3 out.cnf   (both degree sequences, sorted)"""
import sys
from pysat.card import CardEnc, EncType
from enc_quot import build

k = int(sys.argv[1]); spec = sys.argv[2]; g = k - 2
O = list(range(1, g + 1)); I = list(range(g + 1, 2 * g + 1))
if spec.startswith('ab:'):
    # ab:a1,..,a9/b1,..,b9 : row sums of B (in the order of O) and column sums (order of I), both non-increasing.
    # Valid because O and I can be relabelled to sort the degrees; the remaining symmetry is the product of the
    # symmetric groups of the blocks of equal degree, and lex-leader is applied only to transpositions inside blocks.
    al, be = spec[3:].split('/'); al = list(map(int, al.split(','))); be = list(map(int, be.split(',')))
    assert al == sorted(al, reverse=True) and be == sorted(be, reverse=True) and sum(al) == sum(be)
    op = [(O[i], O[j]) for i in range(g) for j in range(i + 1, g) if al[i] == al[j]]
    ip = [(I[i], I[j]) for i in range(g) for j in range(i + 1, g) if be[i] == be[j]]
    cnf, pool, a = build(k, sym=True, nf2=True, ntt=True, alltr=True, opairs=op, ipairs=ip)
    for x, r in zip(O, al):
        cnf.extend(CardEnc.equals([a[x, z] for z in I], bound=r, vpool=pool, encoding=EncType.seqcounter).clauses)
    for z, r in zip(I, be):
        cnf.extend(CardEnc.equals([a[x, z] for x in O], bound=r, vpool=pool, encoding=EncType.seqcounter).clauses)
    spec = 'ab'
else:
    cnf, pool, a = build(k, sym=True, nf2=True, ntt=True, alltr=True)
if spec == 'ab':
    pass
elif spec.startswith('row:'):
    r = int(spec[4:])   # only the row sums (out-degree of each x in O into I) fixed to r; column sums free
    for x in O:
        cnf.extend(CardEnc.equals([a[x, z] for z in I], bound=r, vpool=pool, encoding=EncType.seqcounter).clauses)
elif spec.startswith('t:'):
    T = int(spec[2:])
    cnf.extend(CardEnc.equals([a[x, z] for x in O for z in I], bound=T, vpool=pool, encoding=EncType.totalizer).clauses)
else:
    r = int(spec)
    for x in O:
        cnf.extend(CardEnc.equals([a[x, z] for z in I], bound=r, vpool=pool, encoding=EncType.seqcounter).clauses)
    for z in I:
        cnf.extend(CardEnc.equals([a[x, z] for x in O], bound=r, vpool=pool, encoding=EncType.seqcounter).clauses)
cnf.to_file(sys.argv[3])
with open(sys.argv[3] + '.map', 'w') as f:
    import json
    json.dump({'k': k, 'a': [[c, d, v] for (c, d), v in a.items()]}, f)
print(f'k={k} {spec} vars={cnf.nv} clauses={len(cnf.clauses)}')
