#!/usr/bin/env python3
"""OPB (pseudo-Boolean) version of the A-only quotient instance: same variables, normal form, symmetry breaking and
product definitions as enc_quot.py, but degrees and pair conditions as linear constraints:
  out/in-degree = k-2;  2(a_cd + a_dc) + #common out-neighbours = 2;  2(a_cd + a_dc) + #common in-neighbours = 2.
usage: enc_pb.py k out.opb [enc_quot options]"""
import sys
from enc_quot import build
k = int(sys.argv[1]); opts = sys.argv[3:]
pb = []
cnf, pool, a = build(k, sym='--sym' in opts, nf2='--nf2' in opts, ntt='--ntt' in opts, alltr='--alltr' in opts, pb=pb)
def lit(l): return f'x{l}' if l > 0 else f'~x{-l}'
with open(sys.argv[2], 'w') as f:
    f.write(f'* #variable= {cnf.nv} #constraint= {len(cnf.clauses) + len(pb)}\n')
    for cl in cnf.clauses:
        f.write(' '.join(f'+1 {lit(l)}' for l in cl) + ' >= 1 ;\n')
    for terms, op, rhs in pb:
        f.write(' '.join(f'+{c} x{v}' for c, v in terms) + f' {op} {rhs} ;\n')
print(f'k={k} vars={cnf.nv} clauses={len(cnf.clauses)} linear={len(pb)}')
