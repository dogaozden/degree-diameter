# exploratory: Suzuki-Tits ovoid in PG(3,8) and its affine automorphisms (w14)
import itertools, sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/handsoff-49/w14")
import gens14
F = gens14.gf2m(3, 0b1011)          # GF(8), x^3+x+1
M, A, L, E = F.M, F.A, F.log, F.exp
def pw(a, e):
    if a == 0: return 0 if e > 0 else 1
    return E[(L[a] * e) % 7]
sig = 4                              # sigma: x -> x^4  (sigma^2 = Frobenius on GF(8))
def f(x, y):
    t = pw(x, sig + 2)
    t = A[t][M[x][y]]
    t = A[t][pw(y, sig)]
    return t
pts = [(1, x, y, f(x, y)) for x in range(8) for y in range(8)] + [(0, 0, 0, 1)]
def norm(v):
    for x in v:
        if x:
            inv = next(b for b in range(1, 8) if M[x][b] == 1)
            return tuple(M[inv][t] for t in v)
def det_zero(u, v, w):  # rank<=2 of 3 vectors in GF(8)^4 -> collinear test via rank
    rows = [list(u), list(v), list(w)]
    r = 0; cols = 4
    rows = [row[:] for row in rows]
    for c in range(cols):
        piv = next((i for i in range(r, 3) if rows[i][c]), None)
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = next(b for b in range(1, 8) if M[rows[r][c]][b] == 1)
        rows[r] = [M[inv][t] for t in rows[r]]
        for i in range(3):
            if i != r and rows[i][c]:
                fac = rows[i][c]
                rows[i] = [A[rows[i][k]][M[fac][rows[r][k]]] for k in range(4)]
        r += 1
    return r <= 2
bad = 0
for a, b, c in itertools.combinations(pts, 3):
    if det_zero(a, b, c): bad += 1
print("points", len(set(map(norm, pts))), "collinear triples", bad)

# ---- automorphisms of the ovoid
O = [norm(p) for p in pts]
Oset = set(O)
idx = {p: i for i, p in enumerate(O)}
def apply(Mx, v):
    out = []
    for row in Mx:
        s = 0
        for a_, b_ in zip(row, v):
            s = A[s][M[a_][b_]]
        out.append(s)
    return norm(out)
def preserves(Mx):
    return all(apply(Mx, p) in Oset for p in O)
# affine translations-type maps (coordinates homogeneous (X0,X1,X2,X3) = (1,x,y,z))
def tr_mat(a, b):
    sa = pw(a, sig)
    c1 = A[b][pw(a, sig + 1)]
    c3 = A[A[pw(a, sig + 2)][M[a][b]]][pw(b, sig)]
    # z' = z + c1*x + a*y + c3
    Mx = [[1, 0, 0, 0], [a, 1, 0, 0], [b_ := A[b][sa] if False else A[b][0] if False else 0, 0, 0, 0], [0, 0, 0, 0]]
    # build explicitly: x' = x + a ; y' = y + a^sig x + b ; z' = z + c1 x + a y + c3
    Mx = [[1, 0, 0, 0],
          [a, 1, 0, 0],
          [b, sa, 1, 0],
          [c3, c1, a, 1]]
    return Mx
def diag_mat(r):
    return [[1, 0, 0, 0], [0, r, 0, 0], [0, 0, pw(r, sig + 1), 0], [0, 0, 0, pw(r, sig + 2)]]
ok_t = all(preserves(tr_mat(a_, b_)) for a_ in range(8) for b_ in range(8))
ok_d = all(preserves(diag_mat(r)) for r in range(1, 8))
print("affine translations preserve O:", ok_t, " diagonal:", ok_d)
# monomial search for an element swapping infinity (0:0:0:1) with origin (1:0:0:0)
found = []
for perm in itertools.permutations(range(4)):
    for d in itertools.product(range(1, 8), repeat=3):
        dd = (1,) + d
        Mx = [[0] * 4 for _ in range(4)]
        for i in range(4):
            Mx[i][perm[i]] = dd[i]
        if preserves(Mx):
            found.append((perm, dd))
print("monomial preservers (incl. diagonal):", len(found))
print([x for x in found if x[0] != (0, 1, 2, 3)][:10])

def perm_of(Mx):
    return tuple(idx[apply(Mx, p)] for p in O)
w_mat = [[0, 0, 0, 1], [0, 0, 1, 0], [0, 1, 0, 0], [1, 0, 0, 0]]
gens = [perm_of(tr_mat(a_, b_)) for (a_, b_) in [(1, 0), (0, 1), (2, 0), (0, 2), (4, 0), (0, 4)]]
gens.append(perm_of(diag_mat(2)))
gens.append(perm_of(w_mat))
from collections import deque
ident = tuple(range(65)); seen = {ident}; dq = deque([ident])
while dq:
    g = dq.popleft()
    for s in gens:
        h = tuple(g[x] for x in s)
        if h not in seen:
            seen.add(h); dq.append(h)
print("group order generated:", len(seen))
import json
json.dump([list(g) for g in gens], open("/home/user/degree-diameter/research/squads/handsoff-49/w14/sz/sz8_gens.json", "w"))
