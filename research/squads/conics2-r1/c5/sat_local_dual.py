#!/usr/bin/env python3
"""Card c5 (wildcard): exact SAT search for the largest freed set R of H(q) such that a bijection sigma (points -> lines)
satisfies (L) local duality at every x in R: sigma(Gamma2(x)) = Gamma2(sigma(x)), and optionally (N1) R non-collinear.
Increases k until UNSAT (or time out) and writes each model as a 'multi'-free pair of files (sigma, R) that
tools/transcheck.py scores exactly.
usage: sat_local_dual.py HEXBIN OUTDIR [--n1] [--k0 K] [--kmax K]"""
import sys, os, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/tools')
from hexload import load
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

hexfn, outdir = sys.argv[1], sys.argv[2]
n1 = '--n1' in sys.argv
k0 = int(sys.argv[sys.argv.index('--k0') + 1]) if '--k0' in sys.argv else 1
kmax = int(sys.argv[sys.argv.index('--kmax') + 1]) if '--kmax' in sys.argv else 10**9
os.makedirs(outdir, exist_ok=True)
q, N, LP, PL, X = load(hexfn)
lines_of = [set(PL[p]) for p in range(N)]
points_of = [set(LP[l]) for l in range(N)]
# meet[m]: lines l != m meeting m
meet = []
for m in range(N):
    s = set()
    for p in LP[m]:
        s.update(PL[p])
    s.discard(m)
    meet.append(sorted(s))
# Gamma2(x): points collinear with x, x excluded
gam2 = []
for x in range(N):
    s = set()
    for l in PL[x]:
        s.update(LP[l])
    s.discard(x)
    gam2.append(sorted(s))

top = [0]
def new():
    top[0] += 1
    return top[0]
S = np.zeros((N, N), np.int64)
for p in range(N):
    for l in range(N):
        S[p, l] = new()
F = [new() for _ in range(N)]
A = {}
clauses = []
for p in range(N):
    for m in range(N):
        pass
# bijection
for p in range(N):
    enc = CardEnc.equals(lits=[int(v) for v in S[p]], bound=1, top_id=top[0], encoding=EncType.seqcounter)
    top[0] = max(top[0], enc.nv); clauses.extend(enc.clauses)
for l in range(N):
    enc = CardEnc.equals(lits=[int(v) for v in S[:, l]], bound=1, top_id=top[0], encoding=EncType.seqcounter)
    top[0] = max(top[0], enc.nv); clauses.extend(enc.clauses)
# a[p][m] <-> sigma(p) meets m (only the direction a -> OR, which is what is needed)
for p in range(N):
    for m in range(N):
        a = new(); A[(p, m)] = a
        clauses.append([-a] + [int(S[p, l]) for l in meet[m]])
# (L): x freed and sigma(x) = m  ->  sigma(p) meets m for all p in Gamma2(x)
for x in range(N):
    for m in range(N):
        for p in gam2[x]:
            clauses.append([-F[x], -int(S[x, m]), A[(p, m)]])
if n1:
    for x in range(N):
        for y in gam2[x]:
            if y > x:
                clauses.append([-F[x], -F[y]])
print(f'q={q} N={N} vars={top[0]} clauses={len(clauses)} n1={n1}', flush=True)

k = k0
best = None
while k <= kmax:
    t0 = time.time()
    card = CardEnc.atleast(lits=F, bound=k, top_id=top[0], encoding=EncType.seqcounter)
    with Solver(name='cd19', bootstrap_with=clauses + card.clauses) as s:
        ok = s.solve()
        dt = time.time() - t0
        print(f'k={k} sat={ok} time={dt:.1f}s', flush=True)
        if not ok:
            break
        mdl = set(v for v in s.get_model() if v > 0)
        sig = np.array([[l for l in range(N) if S[p, l] in mdl][0] for p in range(N)], np.int64)
        R = [x for x in range(N) if F[x] in mdl]
        assert len(R) >= k and len(set(sig.tolist())) == N
        best = (sig, R)
        with open(os.path.join(outdir, f'sigma_k{len(R)}.txt'), 'w') as f:
            f.write('\n'.join(map(str, sig.tolist())) + '\n')
        with open(os.path.join(outdir, f'R_k{len(R)}.txt'), 'w') as f:
            f.write(' '.join(map(str, R)) + '\n')
        print(f'found |R|={len(R)}', flush=True)
    k = len(R) + 1
print('best', None if best is None else len(best[1]), flush=True)
