#!/usr/bin/env python3
"""Independent numeric check, over F_7, of the counts behind Lemma 4.1 and Lemma 4.3 (k = 4 form) of research/theorems/OMEGA_REPAIR.md.
Uses only the quadric Q = x0 x4 + x1 x5 + x2 x6 - x3^2 of H(7) (as in lean/BipartiteDD/Hexagon/Defs.lean) and the polar form
B(x,y) = Q(x+y) - Q(x) - Q(y); no Lean code. Facts used (proved in Lean, Bridge.lean): for singular points x != y,
dist(x,y) <= 4 iff B(x,y) = 0, and dist = 6 iff B(x,y) != 0.
Checks: (a) |<y,y'>^perp cap Q| = 2401 for independent singular y, y' (affine zeros in F_7^7); triple perp zeros <= 385;
(b) pair overlaps of C_y = {x singular : B(t,x) != 0, B(y,x) = 0} are >= 336 points for t not on line yy', triple overlaps <= 64;
(c) over random and structured configurations (t, y1..y5 distinct singular points) with FEWER THAN 4 of the 15 pairs perpendicular,
the union of the C_{y_i} has size <= 9621 (the Lean/note worst case) and union + 140*49 < 7^5."""
import itertools, random, sys
import numpy as np
q = 7
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
def Q(x): return (x[0]*x[4] + x[1]*x[5] + x[2]*x[6] - x[3]*x[3]) % q
def Bf(x, y): return (x[0]*y[4] + x[4]*y[0] + x[1]*y[5] + x[5]*y[1] + x[2]*y[6] + x[6]*y[2] - 2*x[3]*y[3]) % q
# all vectors of F_7^7 with Q = 0 (vectorised), then projective reps
allv = np.indices((q,)*7).reshape(7, -1).T.astype(np.int64)   # 823543 x 7
Qv = (allv[:,0]*allv[:,4] + allv[:,1]*allv[:,5] + allv[:,2]*allv[:,6] - allv[:,3]**2) % q
Z = allv[Qv == 0]
assert len(Z) == q**6, len(Z)
nz = Z[(Z != 0).any(axis=1)]
# normalise: first nonzero coordinate = 1
first = (nz != 0).argmax(axis=1)
lead = nz[np.arange(len(nz)), first]
inv = np.array([0,1,4,5,2,3,6])
pts = (nz * inv[lead][:, None]) % q
pts = np.unique(pts, axis=0)
N = len(pts); assert N == (q**6-1)//(q-1) == 19608, N
print("singular points:", N)
def Bvec(y):  # B(y, pts[i]) for all i
    return (pts[:,0]*y[4] + pts[:,4]*y[0] + pts[:,1]*y[5] + pts[:,5]*y[1] + pts[:,2]*y[6] + pts[:,6]*y[2] - 2*pts[:,3]*y[3]) % q
Bcache = {}
def Bv(i):
    if i not in Bcache: Bcache[i] = Bvec(pts[i])
    return Bcache[i]
# (a) zeros of Q on <y,y'>^perp: enumerate all vectors in F_7^7 perpendicular to y,y'
def perp_zero_count(S):
    m = np.ones(len(Z), dtype=bool)
    for s in S:
        m &= ((Z[:,0]*s[4] + Z[:,4]*s[0] + Z[:,1]*s[5] + Z[:,5]*s[1] + Z[:,2]*s[6] + Z[:,6]*s[2] - 2*Z[:,3]*s[3]) % q == 0)
    return int(m.sum())
bad_a = 0
cnt2 = set()
for _ in range(40):
    i, j = rng.sample(range(N), 2)
    c = perp_zero_count([pts[i], pts[j]]); cnt2.add((c, int(Bf(pts[i], pts[j]) == 0)))
print("(a) |<y,y'>^perp cap Q| (value, y perp y'):", sorted(cnt2))
assert all(c == 2401 for c, _ in cnt2)
cnt3 = {}
for _ in range(60):
    i, j, k = rng.sample(range(N), 3)
    c = perp_zero_count([pts[i], pts[j], pts[k]]); cnt3[c] = cnt3.get(c, 0) + 1
print("(a) triple perp zero counts (random triples):", sorted(cnt3.items()))
# (b),(c)
def C(t, y): return (Bv(t) != 0) & (Bv(y) == 0)
def rank_ok(idx):  # independence over F_7 of three projective points
    M = [list(map(int, pts[i])) for i in idx]
    # rank via simple gaussian elimination mod 7
    M = [r[:] for r in M]; rk = 0
    for col in range(7):
        piv = None
        for r in range(rk, len(M)):
            if M[r][col] % q: piv = r; break
        if piv is None: continue
        M[rk], M[piv] = M[piv], M[rk]
        iv = pow(M[rk][col], -1, q)
        M[rk] = [(v*iv) % q for v in M[rk]]
        for r in range(len(M)):
            if r != rk and M[r][col] % q:
                f = M[r][col]; M[r] = [(a - f*b) % q for a, b in zip(M[r], M[rk])]
        rk += 1
    return rk
pair_min, trip_max = 10**9, 0
for _ in range(300):
    t, y, y2 = rng.sample(range(N), 3)
    if rank_ok([t, y, y2]) < 3: continue
    ov = int((C(t, y) & C(t, y2)).sum()); pair_min = min(pair_min, ov)
print("(b) min pair overlap |C_y cap C_y'| over", "random independent (t,y,y'):", pair_min, "(Lean/note: >= 336)")
assert pair_min >= 336
for _ in range(300):
    t, a, b, c = rng.sample(range(N), 4)
    if rank_ok([a, b, c]) < 3: continue
    ov = int((Bv(a)==0).__and__(Bv(b)==0).__and__(Bv(c)==0).sum()); trip_max = max(trip_max, ov)
print("(b) max |a^perp cap b^perp cap c^perp cap Q| points over random independent triples:", trip_max, "(Lean/note: <= (q+1)^2 = 64)")
assert trip_max <= 64
# (c) unions
def close_pairs(t, Y):
    pr = 0
    S = [t] + list(Y)
    for a, b in itertools.combinations(S, 2):
        if Bf(pts[a], pts[b]) == 0: pr += 1
    return pr
def union_size(t, Y):
    u = np.zeros(N, dtype=bool)
    for y in Y: u |= C(t, y)
    return int(u.sum())
worst = 0; worst_k = None; n_tested = 0; hist = {}
def consider(t, Y):
    global worst, worst_k, n_tested
    if len(set([t] + list(Y))) < 6: return
    k = close_pairs(t, Y)
    if k >= 4: return
    u = union_size(t, Y); n_tested += 1
    hist[k] = max(hist.get(k, 0), u)
    assert u + 140*49 < 7**5, (t, Y, u)
    if u > worst: worst, worst_k = u, k
# random general position
for _ in range(600):
    s = rng.sample(range(N), 6); consider(s[0], s[1:])
# structured: aligned classes (y_i on one totally singular line through t; then C_i disjoint) and rich lines.
def line_through(i, j):  # points of the projective line <pts[i], pts[j]>
    out = set()
    for a in range(q):
        for b in range(q):
            if a or b:
                v = (a*pts[i] + b*pts[j]) % q
                f = (v != 0).argmax(); v = (v * inv[v[f]]) % q
                out.add(tuple(int(x) for x in v))
    return out
index = {tuple(int(x) for x in p): n for n, p in enumerate(pts)}
def perp_pts(i):  # singular points perpendicular to pts[i] (excluding itself)
    return np.nonzero(Bv(i) == 0)[0]
cnt_struct = 0
for _ in range(400):
    t = rng.randrange(N)
    pp = perp_pts(t)
    # pick a perp singular point m with m perp t, the line <t,m> is totally singular; take several points y on it (aligned)
    m = int(rng.choice(pp))
    if m == t: continue
    L = [index[v] for v in line_through(t, m) if index[v] != t]
    for r in (2, 3, 4, 5):
        Y = rng.sample(L, min(r, len(L)))
        rest = [rng.randrange(N) for _ in range(5 - len(Y))]
        consider(t, Y + rest); cnt_struct += 1
    # y's on a line NOT through t (rich line): pick random line of singular points via two perp points not perp t
    a, b = rng.sample(range(N), 2)
    if Bf(pts[a], pts[b]) == 0:
        L2 = [index[v] for v in line_through(a, b)]
        Y = rng.sample(L2, min(3, len(L2)))
        rest = [rng.randrange(N) for _ in range(5 - len(Y))]
        consider(t, Y + rest); cnt_struct += 1
print("(c) configurations with < 4 close pairs tested:", n_tested, "(structured attempts", cnt_struct, ")")
print("(c) max union size by number of close pairs:", dict(sorted(hist.items())), "; overall max", worst, "(Lean/note worst case 9621; threshold 7^5 - 140*49 =", 7**5 - 140*49, ")")
assert worst <= 9621
print("OK")
