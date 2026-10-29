# Independent SAT check of the Section 1.5 claim "k=6 self-polar extension of PG(2,5) impossible; k=5 possible".
# Model (weakest reasonable reading, so UNSAT here implies the claim): conic polarity theta of PG(2,q), q=5;
# k new points P_i and k new lines N_i with theta-hat(P_i)=N_i (self-polar tie), all old incidences kept,
# every old element of degree <= q+2 after adding, every point collinear with every point (diameter 3, Lemma 0.1a).
# Variables: x[i][L] new point i on old line L; z[i][m]=z[m][i] new point i on new line m.
# Old point p on new line m  <=>  x[m][theta(p)]  (tie: (P_m, theta(p)) is the image of (p, N_m)).
# Usage: python3 sat_c4.py Q K
import sys, itertools, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics-r2/c4')
from check_c4 import run
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
q = int(sys.argv[1]); k = int(sys.argv[2])
E = run(q)
N, th_pt, th_ln = E['N'], E['th_pt'], E['th_ln']
pool = IDPool()
cls = []
def x(i, L): return pool.id(('x', i, L))
def z(i, m):
    a, b = min(i, m), max(i, m); return pool.id(('z', a, b))
def inc(i, j): return E['inc'](i, j)
def AND(a, b):
    v = pool.id(('and', min(a, b), max(a, b)))
    cls.extend([[-v, a], [-v, b], [v, -a, -b]]); return v
def atmost(lits, b):
    enc = CardEnc.atmost(lits=lits, bound=b, vpool=pool, encoding=EncType.seqcounter)
    cls.extend(enc.clauses)
def atleast_one(lits): cls.append(list(lits))
def y(p, m): return x(m, th_pt(p))   # old point p on new line m
# degree: each old line gets at most one new point (old points: q+1 + new points on it <= q+2)
for L in range(N):
    atmost([x(i, L) for i in range(k)], 1)
# new point degree: old lines through it + new lines through it <= q+2
for i in range(k):
    lits = [x(i, L) for L in range(N)] + [z(i, m) for m in range(k)]
    atmost(lits, q + 2)
# diameter 3: new point i and old point p collinear
for i in range(k):
    for p in range(N):
        cl = [x(i, L) for L in range(N) if inc(p, L)] + [AND(z(i, m), y(p, m)) for m in range(k)]
        atleast_one(cl)
# new points i, i' collinear
for i, i2 in itertools.combinations(range(k), 2):
    cl = [AND(x(i, L), x(i2, L)) for L in range(N)] + [AND(z(i, m), z(i2, m)) for m in range(k)]
    atleast_one(cl)
t0 = time.time()
with Solver(name='cadical153', bootstrap_with=cls) as s:
    r = s.solve()
    print('q', q, 'k', k, 'SAT' if r else 'UNSAT', 'vars', pool.top, 'clauses', len(cls), 'time %.1fs' % (time.time() - t0))
    if r:
        mdl = set(v for v in s.get_model() if v > 0)
        sol = {i: [L for L in range(N) if x(i, L) in mdl] for i in range(k)}
        print('new point -> old lines:', sol)
