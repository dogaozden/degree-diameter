"""c4: keep the base fixed, free sigma on the points of the demand graphs (and preimages of demanded lines),
solve the induced permutation with SAT over the demand constraints, then check the full structural cost.
Demand (points): same-side pair x,z (pure distance >= 4, <= 1 non-backtracking 4-walk) needs sigma(x), sigma(z) concurrent.
Demand (lines):  same-side pair l,m needs sigma^-1(l), sigma^-1(m) collinear.
usage: satdemand.py base.in sigma_out_prefix [extra_points_file]"""
import sys, time
from collections import Counter
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r2-d11D5/c4')
from fail import load, failing
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

BASE, OUTP = sys.argv[1], sys.argv[2]
EXTRA = [int(v) for v in open(sys.argv[3]).read().split()] if len(sys.argv) > 3 else []
t0 = time.time()
n, dg, ln, sig = load(BASE)
pt = [[] for _ in range(n)]
for l in range(n):
    for p in ln[l]: pt[p].append(l)
Coll = [set() for _ in range(n)]          # points sharing a line
for l in range(n):
    for p in ln[l]: Coll[p].update(ln[l])
for p in range(n): Coll[p].discard(p)
Conc = [set() for _ in range(n)]          # lines sharing a point
for p in range(n):
    for l in pt[p]: Conc[l].update(pt[p])
for l in range(n): Conc[l].discard(l)

def demands(adj1, adj2):
    res = []
    for x in range(n):
        c2 = set()
        for a in adj1[x]:
            for y in adj2[a]:
                if y != x: c2.add(y)
        c4 = Counter()
        for a in adj1[x]:
            for y in adj2[a]:
                if y == x: continue
                for b in adj1[y]:
                    if b == a: continue
                    for z in adj2[b]:
                        if z != y: c4[z] += 1
        for z in range(x + 1, n):
            if z in c2: continue
            if c4[z] <= 1: res.append((x, z))
    return res

dP = demands(pt, ln)     # point pairs
dL = demands(ln, pt)     # line pairs
inv = [0] * n
for p in range(n): inv[sig[p]] = p
VP = sorted({v for e in dP for v in e})
VL = sorted({v for e in dL for v in e})
F = sorted(set(VP) | {inv[l] for l in VL} | set(EXTRA))
Fset = set(F)
S = sorted({sig[p] for p in F})
Sset = set(S)
print("demands: points", len(dP), "lines", len(dL), "| free points", len(F), "free lines", len(S), flush=True)

pool = IDPool()
def V(p, l): return pool.id(('v', p, l))
clauses = []
for p in F:
    enc = CardEnc.equals(lits=[V(p, l) for l in S], bound=1, vpool=pool, encoding=EncType.seqcounter)
    clauses += enc.clauses
for l in S:
    enc = CardEnc.equals(lits=[V(p, l) for p in F], bound=1, vpool=pool, encoding=EncType.seqcounter)
    clauses += enc.clauses
# (a) point demands: sigma(z) concurrent with sigma(x)
for x, z in dP:
    for l in S:
        clauses.append([-V(x, l)] + [V(z, m) for m in Conc[l] if m in Sset])
# (b) line demands: sigma^-1(m) collinear with sigma^-1(l)
for l, m in dL:
    for p in F:
        clauses.append([-V(p, l)] + [V(q, m) for q in Coll[p] if q in Fset])
print("clauses", len(clauses), "vars", pool.top, "build %.2fs" % (time.time() - t0), flush=True)

solver = None
for name in ('cadical195', 'glucose4'):
    try:
        solver = Solver(name=name, bootstrap_with=clauses); break
    except Exception as e:
        print("solver", name, "unavailable:", e)
ok = solver.solve()
print("SAT" if ok else "UNSAT", "solve %.2fs" % (time.time() - t0), flush=True)
if ok:
    model = set(x for x in solver.get_model() if x > 0)
    sig2 = list(sig)
    for p in F:
        for l in S:
            if V(p, l) in model: sig2[p] = l
    assert sorted(sig2) == list(range(n))
    cost, fails = failing(n, dg, ln, sig2)
    print("full structural cost of SAT solution:", cost, "moved points:", sum(1 for p in range(n) if sig2[p] != sig[p]))
    for s_, t_, c_ in fails[:10]:
        print("  fail s=%d t=%d coset=%d" % (s_, t_, c_))
    with open(OUTP + '.in', 'w') as g:
        g.write("%d %d\n" % (n, dg))
        for l in range(n): g.write(" ".join(map(str, ln[l])) + "\n")
        for p in range(n): g.write("%d\n" % sig2[p])
    print("wrote", OUTP + '.in')
