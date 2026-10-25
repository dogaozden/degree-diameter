"""c4: enumerate demand-satisfying sigma' moving <= K points of F (demand points + preimages), score each by full cost.
usage: enum4.py base.in K maxsol timelimit_s outprefix"""
import sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r2-d11D5/c4')
from fail import load, failing
from satdemand_lib import build_demands
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
BASE, K, MAXS, TL, OUTP = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]), sys.argv[5]
t0 = time.time()
n, dg, ln, sig, pt, Coll, Conc, dP, dL = build_demands(BASE)
inv = [0] * n
for p in range(n): inv[sig[p]] = p
VP = sorted({v for e in dP for v in e}); VL = sorted({v for e in dL for v in e})
F = sorted(set(VP) | {inv[l] for l in VL}); Fset = set(F)
S = sorted({sig[p] for p in F}); Sset = set(S)
pool = IDPool()
def V(p, l): return pool.id(('v', p, l))
cl = []
for p in F: cl += CardEnc.equals(lits=[V(p, l) for l in S], bound=1, vpool=pool, encoding=EncType.seqcounter).clauses
for l in S: cl += CardEnc.equals(lits=[V(p, l) for p in F], bound=1, vpool=pool, encoding=EncType.seqcounter).clauses
for x, z in dP:
    for l in S: cl.append([-V(x, l)] + [V(z, m) for m in Conc[l] if m in Sset])
for l, m in dL:
    for p in F: cl.append([-V(p, l)] + [V(q, m) for q in Coll[p] if q in Fset])
cl += CardEnc.atmost(lits=[-V(p, sig[p]) for p in F], bound=K, vpool=pool, encoding=EncType.seqcounter).clauses
s = Solver(name='cadical195', bootstrap_with=cl)
best = (10**9, None); hist = {}; cnt = 0
while cnt < MAXS and time.time() - t0 < TL:
    if not s.solve(): print("exhausted after", cnt, "solutions"); break
    model = set(x for x in s.get_model() if x > 0)
    sig2 = list(sig)
    for p in F:
        for l in S:
            if V(p, l) in model: sig2[p] = l
    cost, _ = failing(n, dg, ln, sig2, want_list=False)
    cnt += 1
    hist[cost] = hist.get(cost, 0) + 1
    if cost < best[0]:
        best = (cost, sig2[:])
        print("new best cost", cost, "moved", sum(1 for p in range(n) if sig2[p] != sig[p]), "after", cnt, flush=True)
        if cost == 0: break
    s.add_clause([-V(p, sig2[p]) for p in F])
print("solutions", cnt, "best", best[0], "cost histogram (lowest 10)", sorted(hist.items())[:10], "time %.1f" % (time.time() - t0))
if best[1] is not None:
    with open(OUTP + '_best.in', 'w') as g:
        g.write("%d %d\n" % (n, dg))
        for l in range(n): g.write(" ".join(map(str, ln[l])) + "\n")
        for p in range(n): g.write("%d\n" % best[1][p])
    print("wrote", OUTP + '_best.in')
