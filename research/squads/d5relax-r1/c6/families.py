"""Card c6 (algebraic families) of squad d5relax-r1.  Each family is a set of points of PG(3,q) defined by an
equation or a construction.  For every sampled member: raw size, thinned size (greedily delete the point with the most
collinear partners inside the set until the set is relaxed; randomised tie-breaks, best of several runs), and thinned +
greedy augmentation (add points that keep the set relaxed).   usage: python3 families.py q [samples]"""
import sys, os, json, random, time
import numpy as np
D = '/home/user/degree-diameter/research/theorems/d5relax'
OUT = '/home/user/degree-diameter/research/squads/d5relax-r1/c6'
sys.path.insert(0, D)
from orbits import WSp

q = int(sys.argv[1]); NS = int(sys.argv[2]) if len(sys.argv) > 2 else 300
rng = random.Random(1000 + q)
W = WSp(q); n = W.n; P = W.P
SQ = set((x * x) % q for x in range(1, q))
NONSQ = min(a for a in range(1, q) if a not in SQ)
sqtab = np.array([0] + [1 if a in SQ else -1 for a in range(1, q)])
def chi(v): return sqtab[np.asarray(v) % q]

PAIRS = [(i, j) for i in range(4) for j in range(i, 4)]
MON2 = [(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2)]
MON3 = MON2 + [(3, 0), (2, 1), (1, 2), (0, 3)]
def qeval(c, V):
    s = np.zeros(len(V), dtype=np.int64)
    for k, (i, j) in enumerate(PAIRS): s += c[k] * V[:, i] * V[:, j]
    return s % q
def rand_form(mode='full'):
    if mode == 'full': return [rng.randrange(q) for _ in range(10)]
    c = [0] * 10
    for k in rng.sample(range(10), rng.choice([2, 3])):  # sparse, e.g. x0^2 + c x1^2
        c[k] = rng.randrange(1, q)
    return c
def poly(cf, mons, X, Y):
    s = np.zeros_like(X)
    for c, (a, b) in zip(cf, mons): s = (s + c * (X ** a) * (Y ** b)) % q
    return s
def named(d):
    c = [0] * 10
    for (i, j), v in d.items(): c[PAIRS.index((i, j))] = v % q
    return c

def is_relaxed(T):
    T = np.asarray(T, dtype=np.int64)
    return len(T) == 0 or int(W.C[np.ix_(T, T)].sum(1).max()) <= 1

def thin_aug(S, tries=6):
    S = np.unique(np.asarray(S, dtype=np.int64))
    if len(S) == 0: return 0, 0, []
    sub = W.C[np.ix_(S, S)].astype(np.int32)
    best = None
    for t in range(tries):
        alive = np.ones(len(S), bool); deg = sub.sum(1)
        while True:
            dm = np.where(alive, deg, -1); mx = dm.max()
            if mx <= 1: break
            cand = np.flatnonzero(dm == mx)
            i = int(cand[0]) if t == 0 else int(cand[rng.randrange(len(cand))])
            alive[i] = False; deg = deg - sub[:, i]
        keep = S[alive]
        if best is None or len(keep) > len(best): best = keep
    th = len(best)
    inT = np.zeros(n, bool); inT[best] = True
    while True:   # greedy augmentation: x may be added if it has <=1 partner in T and no partner has degree 1 in T
        dT = W.C[:, inT].sum(1)
        deg1 = inT & (dT == 1)
        addable = (~inT) & (dT <= 1) & ~W.C[:, deg1].any(1)
        if not addable.any(): break
        cand = np.flatnonzero(addable); inT[cand[rng.randrange(len(cand))]] = True
    T = [int(x) for x in np.flatnonzero(inT)]
    assert is_relaxed(T)
    return th, len(T), T

stats = {}
def record(name, S, params):
    raw = len(np.unique(np.asarray(S)))
    th, au, T = thin_aug(S)
    st = stats.setdefault(name, dict(n=0, raw=[], thin=[], aug=[], best=(-1, None, None)))
    st['n'] += 1; st['raw'].append(raw); st['thin'].append(th); st['aug'].append(au)
    if au > st['best'][0]: st['best'] = (au, T, params)

t0 = time.time()
grid_x = np.repeat(np.arange(q), q); grid_y = np.tile(np.arange(q), q); tt = np.arange(q)
ones_g = np.ones(q * q, dtype=np.int64); zer = np.zeros(q, dtype=np.int64)
# A: graphs (1,x,y,f(x,y)) [+ (0,1,y,g(y))]
for _ in range(NS):
    cf = [rng.randrange(q) for _ in range(6)]
    S1 = W.index(np.stack([ones_g, grid_x, grid_y, poly(cf, MON2, grid_x, grid_y)], 1))
    record('A1 graph f quadratic (q^2 pts)', S1, dict(f=cf))
    cg = [rng.randrange(q) for _ in range(3)]
    S2 = W.index(np.stack([zer, np.ones(q, dtype=np.int64), tt, poly(cg + [0], [(0, 0), (0, 1), (0, 2), (0, 3)], zer, tt)], 1))
    record('A2 graph f quad + infinity g quad (q^2+q)', np.concatenate([S1, S2]), dict(f=cf, g=cg))
    cf3 = [rng.randrange(q) for _ in range(10)]
    S3 = W.index(np.stack([ones_g, grid_x, grid_y, poly(cf3, MON3, grid_x, grid_y)], 1))
    cg3 = [rng.randrange(q) for _ in range(4)]
    S4 = W.index(np.stack([zer, np.ones(q, dtype=np.int64), tt, poly(cg3, [(0, 0), (0, 1), (0, 2), (0, 3)], zer, tt)], 1))
    record('A3 graph f cubic + infinity g cubic', np.concatenate([S3, S4]), dict(f=cf3, g=cg3))
# B: quadric zero sets
for _ in range(NS):
    c = rand_form('full')
    record('B1 random quadric Q=0', np.flatnonzero(qeval(c, P) == 0), dict(Q=c))
for nm, d in [('B2 elliptic x0x1+x2^2-n x3^2', {(0, 1): 1, (2, 2): 1, (3, 3): -NONSQ}),
              ('B2 hyperbolic x0x1+x2x3', {(0, 1): 1, (2, 3): 1}),
              ('B2 cone x0x1+x2^2', {(0, 1): 1, (2, 2): 1})]:
    c = named(d)
    record(nm, np.flatnonzero(qeval(c, P) == 0), dict(Q=c))
# C: Q1=0 with chi(Q2), and chi(Q1), chi(Q2) conditions
for _ in range(NS):
    m = rng.choice(['full', 'diag'])
    c1, c2 = rand_form(m), rand_form(m)
    v1, v2 = qeval(c1, P), qeval(c2, P)
    record('C1 Q1=0 & chi(Q2)=-1', np.flatnonzero((v1 == 0) & (chi(v2) == -1)), dict(Q1=c1, Q2=c2))
    record('C2 Q1=0 & chi(Q2)=+1', np.flatnonzero((v1 == 0) & (chi(v2) == 1)), dict(Q1=c1, Q2=c2))
    e1, e2 = rng.choice([1, -1]), rng.choice([1, -1])
    record('C3 chi(Q1)=e1 & chi(Q2)=e2', np.flatnonzero((chi(v1) == e1) & (chi(v2) == e2)), dict(Q1=c1, Q2=c2, e=[e1, e2]))
# D: norm conditions on F_{q^2} = F_q(i), i^2 = NONSQ; x = (a,b), a = x0 + x1 i, b = x2 + x3 i
a0, a1, b0, b1 = P[:, 0], P[:, 1], P[:, 2], P[:, 3]
for l0 in range(q):
    for l1 in range(q):
        u0 = (a0 - (l0 * b0 + NONSQ * l1 * b1)) % q; u1 = (a1 - (l0 * b1 + l1 * b0)) % q
        Nu = (u0 * u0 - NONSQ * u1 * u1) % q
        for e in (1, -1):
            record('D1 chi(N(a-lam b))=e (lam in F_q^2)', np.flatnonzero(chi(Nu) == e), dict(lam=[l0, l1], e=e))
# E: translates (Sp(4,q)) of a twisted cubic (1,t,t^2,t^3)+(0,0,0,1) and a conic (1,t,t^2,0)+(0,0,1,0)
cub = W.index(np.vstack([np.stack([np.ones(q, dtype=np.int64), tt, tt * tt % q, tt ** 3 % q], 1),
                         np.array([[0, 0, 0, 1]])]))
con = W.index(np.vstack([np.stack([np.ones(q, dtype=np.int64), tt, tt * tt % q, zer], 1), np.array([[0, 0, 1, 0]])]))
pool = []
for _ in range(NS):
    g = W.random_element(rng)
    record('E1a Sp-translate of twisted cubic', g[cub], dict(g=None))
    pool.append(g[cub])
    g = W.random_element(rng)
    record('E1b Sp-translate of conic', g[con], dict(g=None))
    pool.append(g[con])
for run in range(5):
    order = list(range(len(pool))); rng.shuffle(order)
    U = np.array([], dtype=np.int64)
    for j in order:
        cand = np.unique(np.concatenate([U, pool[j]]))
        if is_relaxed(cand): U = cand
    record('E2 greedy union of Sp-translates of cubic/conic', U, dict(run=run, raw=len(U)))
print('q=%d families done in %.1f s' % (q, time.time() - t0))

rows = []
best_all = {}
for name, st in stats.items():
    rows.append((name, st['n'], int(np.median(st['raw'])), max(st['raw']), max(st['thin']), int(np.median(st['thin'])),
                 max(st['aug']), int(np.median(st['aug']))))
    best_all[name] = dict(size_aug=st['best'][0], T=st['best'][1], params=st['best'][2])
print('%-48s %5s %8s %6s %8s %8s %8s' % ('family', 'sets', 'raw med', 'raw max', 'thin max', 'thin med', 'aug max'))
for r in rows:
    print('%-48s %5d %8d %6d %8d %8d %8d' % (r[0], r[1], r[2], r[3], r[4], r[5], r[6]))
json.dump(dict(q=q, families=best_all, table=rows), open(os.path.join(OUT, 'fam_best_q%d.json' % q), 'w'))
