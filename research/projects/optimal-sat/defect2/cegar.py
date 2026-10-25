#!/usr/bin/env python3
"""CEGAR for (k,3,-2): solve the A-only quotient instance; for each solution A decide the signing by GF(2)
elimination (signs_gf2.py); if no signing exists, add the clause 'not all arcs of the certificate are present'
(valid: any A containing those arcs has the same odd set of squares, hence no signing) and repeat.
UNSAT at the end means no (k,3,-2)-graph; a signable A means one exists.
usage: cegar.py k [--ntt] [--maxit N] [--log file]"""
import sys, time
import numpy as np
from pysat.solvers import Cadical153
from enc_quot import build
from signs_gf2 import solve as signsolve

k = int(sys.argv[1])
ntt = '--ntt' in sys.argv
maxit = int(sys.argv[sys.argv.index('--maxit') + 1]) if '--maxit' in sys.argv else 10 ** 9
logf = open(sys.argv[sys.argv.index('--log') + 1], 'a') if '--log' in sys.argv else sys.stdout
cnf, pool, a = build(k, sym=True, nf2=True, ntt=ntt)
m = k * (k - 1) // 2
s = Cadical153(bootstrap_with=cnf.clauses)
t0 = time.time(); it = 0
while it < maxit:
    it += 1
    if not s.solve():
        print(f'UNSAT after {it - 1} cuts, {time.time() - t0:.1f} s', file=logf, flush=True); break
    mdl = set(l for l in s.get_model() if l > 0)
    A = np.zeros((m, m), dtype=np.int64)
    for (c, d), v in a.items():
        if v in mdl: A[c, d] = 1
    ok, cert, sq = signsolve(A)
    if ok:
        np.save(f'A_k{k}_signable.npy', A)
        print(f'SIGNABLE solution found at iteration {it}, {time.time() - t0:.1f} s', file=logf, flush=True); break
    arcs = sorted({x for i in cert for x in sq[i]})
    s.add_clause([-a[int(c), int(d)] for c, d in arcs])
    print(f'it {it}: cut with {len(cert)} squares / {len(arcs)} arcs, {time.time() - t0:.1f} s', file=logf, flush=True)
