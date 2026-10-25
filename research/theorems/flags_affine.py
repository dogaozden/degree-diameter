"""Variants of the A_4 flag graph C(2,q) (flags.py) with subspaces removed:
  mode 'H'   : remove every subspace contained in a fixed hyperplane H (affine version)
  mode 'Hp'  : also remove every subspace through a fixed point p not in H (bi-affine; q(q+1)-regular)
  mode 'Hpin': same with p in H
Writes the edge list of the induced flag graph (largest component) and prints degrees and order.
usage: python3 flags_affine.py q mode OUT"""
import itertools, sys
sys.argv_saved = list(sys.argv)
q, mode, out = int(sys.argv[1]), sys.argv[2], sys.argv[3]
n = 5
pts = [v for v in itertools.product(range(q), repeat=n) if next((c for c in v if c), 0) == 1]
pidx = {v: i for i, v in enumerate(pts)}
def norm(v):
    for c in v:
        if c:
            s = pow(c, q - 2, q); return tuple(s * x % q for x in v)
def span(vecs):
    S = set()
    for co in itertools.product(range(q), repeat=len(vecs)):
        v = tuple(sum(c * w[k] for c, w in zip(co, vecs)) % q for k in range(n))
        nv = norm(v)
        if nv is not None: S.add(pidx[nv])
    return frozenset(S)
hyper = [frozenset(i for i, v in enumerate(pts) if sum(a * b for a, b in zip(f, v)) % q == 0) for f in pts]
H = hyper[pidx[(0, 0, 0, 0, 1)]]          # x4 = 0
p = pidx[(0, 0, 0, 0, 1)] if mode == 'Hp' else pidx[(1, 0, 0, 0, 0)]   # (0,0,0,0,1) not in H; (1,0,0,0,0) in H
def ok(S):
    if S <= H: return False
    if mode in ('Hp', 'Hpin') and p in S: return False
    return True
s2 = {}
for a in range(len(pts)):
    for b in range(a + 1, len(pts)):
        S = span([pts[a], pts[b]])
        s2[S] = 1
s2 = list(s2)
s3 = set()
for a in range(len(hyper)):
    for b in range(a + 1, len(hyper)):
        s3.add(hyper[a] & hyper[b])
s3 = list(s3)
P1 = [frozenset([i]) for i in range(len(pts)) if ok(frozenset([i]))]
S2 = [S for S in s2 if ok(S)]; S3 = [S for S in s3 if ok(S)]; S4 = [S for S in hyper if ok(S)]
s2_by_pt = {}
for W in S2:
    for x in W: s2_by_pt.setdefault(x, []).append(W)
s3_of = {W: [U for U in S3 if W <= U] for W in S2}
s4_of = {U: [Hh for Hh in S4 if U <= Hh] for U in S3}
odd, even, edges = {}, {}, []
for P in P1:
    (x,) = tuple(P)
    for W in s2_by_pt.get(x, []):
        for U in s3_of[W]:
            for Hh in s4_of[U]:
                o = odd.setdefault((x, U), len(odd)); e = even.setdefault((W, Hh), len(even)); edges.append((o, e))
No = len(odd); nv = No + len(even)
deg = [0] * nv
for o, e in edges: deg[o] += 1; deg[No + e] += 1
from collections import Counter
print(mode, "q", q, "odd", No, "even", len(even), "vertices", nv, "chambers", len(edges), "degree counts", sorted(Counter(deg).items()))
with open(out, 'w') as f:
    f.write(f"{nv}\n")
    for o, e in edges: f.write(f"{o} {No + e}\n")
