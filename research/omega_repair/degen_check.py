"""Validation of degen.union_bound on Q(6,7): build configurations t, y1..y5 with random degeneracies (points on totally
singular lines through t and on totally singular lines not through t), detect the actual structure from coordinates,
compute the exact |C_1 u ... u C_5| (C_i = y_i^perp & opp(t)) and check exact <= union_bound(structure).
usage: degen_check.py samples seed"""
import sys, random, itertools, numpy as np
sys.path.insert(0, '.')
from geo import Hex
import degen
S = int(sys.argv[1]); rng = random.Random(int(sys.argv[2]))
H = Hex('hex_q7.txt'); F = H.F; n = H.n; P = H.P; q = 7
A, M = F.ADD, F.MUL
def perpv(x):
    s = A[M[P[:, 0], x[4]], M[P[:, 4], x[0]]]; s = A[s, A[M[P[:, 1], x[5]], M[P[:, 5], x[1]]]]; s = A[s, A[M[P[:, 2], x[6]], M[P[:, 6], x[2]]]]
    t = M[P[:, 3], x[3]]; return A[s, F.NEG[A[t, t]]] == 0
def idx(v): v = H.normalize(np.array([v]))[0]; return int(H.lut[(v * H.pwv).sum()])
def rank(vs):
    Mx = np.array(vs, dtype=np.int64); r = 0
    for c in range(7):
        piv = next((i for i in range(r, len(Mx)) if Mx[i, c]), None)
        if piv is None: continue
        Mx[[r, piv]] = Mx[[piv, r]]; Mx[r] = M[F.INV[Mx[r, c]], Mx[r]]
        for i in range(len(Mx)):
            if i != r and Mx[i, c]: Mx[i] = A[Mx[i], M[F.NEG[Mx[i, c]], Mx[r]]]
        r += 1
    return r
def ts_line_points(a, b):                       # the q+1 points of the line ab (a, b point indices)
    return [a] + [idx(A[P[b], M[c, P[a]]]) for c in range(q)]
perp_cache = {}
def pp(i):
    if i not in perp_cache: perp_cache[i] = perpv(P[i])
    return perp_cache[i]
worst, seen = 10 ** 9, {}
for s in range(S):
    t = rng.randrange(n); pt = pp(t)
    ys = []
    def add(y):
        if y != t and y not in ys and len(ys) < 5: ys.append(y)
    def line_through(a):                        # a random totally singular line through point a, as its q+1 points
        while True:
            w = rng.choice(np.flatnonzero(pp(a)).tolist())
            if w != a: return ts_line_points(a, w)
    recipe = rng.randrange(6)
    if recipe == 0:                             # one aligned class of size k
        L = [x for x in line_through(t) if x != t]
        for y in rng.sample(L, rng.randrange(2, 6)): add(y)
    elif recipe == 1:                           # two aligned classes
        for k in (rng.randrange(2, 4), rng.randrange(2, 4)):
            L = [x for x in line_through(t) if x != t]
            for y in rng.sample(L, k): add(y)
    elif recipe in (2, 3):                      # a rich line not through t, then aligned partners
        while True:
            a = rng.randrange(n); L = line_through(a)
            if t not in L: break
        for y in rng.sample(L, rng.randrange(3, 6)): add(y)
        while len(ys) < 5 and rng.random() < 0.7:
            y0 = rng.choice(ys); Lt = ts_line_points(t, y0) if pp(t)[y0] else None
            if Lt: add(rng.choice([x for x in Lt if x not in (t, y0)]))
            else: break
    elif recipe == 4:                           # two rich lines through a common y
        while True:
            a = rng.randrange(n)
            if a != t: break
        for _ in range(2):
            while True:
                L = line_through(a)
                if t not in L: break
            add(a)
            for y in rng.sample([x for x in L if x != a], 2): add(y)
    while len(ys) < 5:
        add(rng.randrange(n))
    # structure
    al = {i: {i} for i in range(5)}
    for i, j in itertools.combinations(range(5), 2):
        if rank([P[t], P[ys[i]], P[ys[j]]]) == 2: al[i] |= {j}; al[j] |= {i}
    part = []
    for i in range(5):
        c = sorted(al[i])
        if c not in part: part.append(c)
    trip = [tr for tr in itertools.combinations(range(5), 3) if rank([P[ys[a]] for a in tr]) == 2 and not any(set(tr) <= set(c) for c in part)]
    lines = []
    for tr in trip:
        L = set(tr)
        for k in range(5):
            if k not in L and rank([P[ys[a]] for a in tr[:2]] + [P[ys[k]]]) == 2: L.add(k)
        L = tuple(sorted(L))
        if L not in lines: lines.append(L)
    if any(len({tuple(x) for x in part}) != len(part) for _ in [0]): pass
    ub = degen.union_bound(part, lines)
    ex = int(np.logical_or.reduce([pp(y) & ~pt for y in ys]).sum())
    key = (tuple(sorted(len(b) for b in part)), tuple(sorted(len(L) for L in lines)))
    seen[key] = seen.get(key, 0) + 1
    worst = min(worst, ub - ex)
    if ex > ub: print("VIOLATION", key, ex, ub)
print(f"{S} configurations, {len(seen)} structure types seen; min (bound - exact union) = {worst}")
for k, v in sorted(seen.items()): print(k, v)
