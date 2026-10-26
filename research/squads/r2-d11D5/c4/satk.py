"""c4: demand-SAT with at most K free points moved from base sigma (F = demand points and preimages of demanded lines).
Then full structural cost check with the bitset mirror.  usage: satk.py base.in K outprefix"""
import sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r2-d11D5/c4')
from fail import load, failing
from satdemand_lib import build_demands
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
BASE, K, OUTP = sys.argv[1], int(sys.argv[2]), sys.argv[3]
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
# at most K points moved: moved_p = not(sigma'(p) == sig[p])
cl += CardEnc.atmost(lits=[-V(p, sig[p]) for p in F], bound=K, vpool=pool, encoding=EncType.seqcounter).clauses
s = Solver(name='cadical195', bootstrap_with=cl)
ok = s.solve()
print("K=%d F=%d %s" % (K, len(F), "SAT" if ok else "UNSAT"), flush=True)
if ok:
    model = set(x for x in s.get_model() if x > 0)
    sig2 = list(sig)
    for p in F:
        for l in S:
            if V(p, l) in model: sig2[p] = l
    assert sorted(sig2) == list(range(n))
    cost, fails = failing(n, dg, ln, sig2)
    moved = [p for p in range(n) if sig2[p] != sig[p]]
    print("  moved", len(moved), "full cost", cost, "fails", fails[:6], flush=True)
    with open(OUTP + '_K%d.in' % K, 'w') as g:
        g.write("%d %d\n" % (n, dg))
        for l in range(n): g.write(" ".join(map(str, ln[l])) + "\n")
        for p in range(n): g.write("%d\n" % sig2[p])
