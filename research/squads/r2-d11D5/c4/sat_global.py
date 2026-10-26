"""c4: demand-only SAT with sigma free on ALL points (no move bound).  UNSAT would prove the demand system alone
(necessary for structural cost 0) is unsatisfiable for this base.  usage: sat_global.py base.in"""
import sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r2-d11D5/c4')
from fail import failing
from satdemand_lib import build_demands
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
t0 = time.time()
n, dg, ln, sig, pt, Coll, Conc, dP, dL = build_demands(sys.argv[1])
print("demands points", len(dP), "lines", len(dL), "build %.1fs" % (time.time() - t0), flush=True)
pool = IDPool()
def V(p, l): return pool.id(('v', p, l))
cl = []
for p in range(n): cl += CardEnc.equals(lits=[V(p, l) for l in range(n)], bound=1, vpool=pool, encoding=EncType.seqcounter).clauses
for l in range(n): cl += CardEnc.equals(lits=[V(p, l) for p in range(n)], bound=1, vpool=pool, encoding=EncType.seqcounter).clauses
for x, z in dP:
    for l in range(n): cl.append([-V(x, l)] + [V(z, m) for m in Conc[l]])
for l, m in dL:
    for p in range(n): cl.append([-V(p, l)] + [V(q, m) for q in Coll[p]])
print("clauses", len(cl), "vars", pool.top, "built %.1fs" % (time.time() - t0), flush=True)
s = Solver(name='cadical195', bootstrap_with=cl)
ok = s.solve()
print("GLOBAL DEMAND-ONLY:", "SAT" if ok else "UNSAT", "%.1fs" % (time.time() - t0), flush=True)
if ok:
    model = set(x for x in s.get_model() if x > 0)
    sig2 = [next(l for l in range(n) if V(p, l) in model) for p in range(n)]
    cost, _ = failing(n, dg, ln, sig2, want_list=False)
    print("full structural cost of demand-only solution:", cost, "moved", sum(1 for p in range(n) if sig2[p] != sig[p]))
