#!/usr/bin/env python3
"""Card c6: SAT (pysat, CaDiCaL) for a dual segment set of H(q) with >= K lines.
x_l: line in G; s_p: point carries >= 2 G-lines (forced by x_l & x_m for l,m through p).
Constraint: for each G-line, at most one point with s_p true (clauses: x_l & s_p & s_p' -> false).
Cardinality sum x_l >= K (totalizer). Symmetry: line 0 in G (H(q) is line-transitive).
usage: sat.py Q K OUTFILE"""
import sys, time, itertools
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/tools')
from hexload import load
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
q = int(sys.argv[1]); K = int(sys.argv[2]); out = sys.argv[3]
qq, N, LP, PL, X = load(f'/home/user/degree-diameter/research/squads/conics2-r1/data/hex_q{q}.bin')
L = N
xv = lambda l: 1 + l
sv = lambda p: 1 + L + p
cl = []
for p in range(N):
    ls = [int(l) for l in PL[p]]
    for a, b in itertools.combinations(ls, 2):
        cl.append([-xv(a), -xv(b), sv(p)])
for l in range(L):
    ps = [int(p) for p in LP[l]]
    for a, b in itertools.combinations(ps, 2):
        cl.append([-xv(l), -sv(a), -sv(b)])
if '--nosym' not in sys.argv: cl.append([xv(0)])                                 # symmetry: line 0 in G
card = CardEnc.atleast(lits=[xv(l) for l in range(L)], bound=K, top_id=1 + 2 * L + 10 * N, encoding=EncType.seqcounter)
cl += card.clauses
t0 = time.time()
with Solver(name='cadical153', bootstrap_with=cl) as S:
    ok = S.solve()
    dt = time.time() - t0
    if ok:
        m = set(v for v in S.get_model() if v > 0)
        G = [l for l in range(L) if xv(l) in m]
        open(out, 'w').write('\n'.join(map(str, G)) + '\n')
        print(f'SAT q={q} K={K} found |G|={len(G)} time={dt:.1f}s', flush=True)
    else:
        print(f'UNSAT q={q} K={K} (no dual segment set with >= {K} lines, given line 0 in G) time={dt:.1f}s', flush=True)
