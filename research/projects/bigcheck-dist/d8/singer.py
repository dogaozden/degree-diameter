"""Singer-type torus of SL(3,q) acting on the split Cayley hexagon H(q) (hexgen coordinates), prime q only.
Writes PERM file: int32 N, int32 order, then N int32 (points image), N int32 (lines image).
x = (X0,X1,X2) -> M x, y = (X4,X5,X6) -> M^{-T} y, X3 fixed; M = multiplication by theta in F_{q^3}, N(theta)=1."""
import sys, itertools, numpy as np, hexlib
path, out = sys.argv[1], sys.argv[2]
q, lines, coord = hexlib.load(path); N = len(coord)
assert all(q % t for t in range(2, q)), "prime q only"
# irreducible cubic h(x) = x^3 + a x^2 + b x + c
def irreducible(a, b, c): return all((x**3 + a*x*x + b*x + c) % q for x in range(q))
h = next((a, b, c) for a in range(q) for b in range(q) for c in range(1, q) if irreducible(a, b, c))
def mul(u, v):  # elements of F_q[x]/h as length-3 lists low..high
    r = [0]*5
    for i in range(3):
        for j in range(3): r[i+j] += u[i]*v[j]
    a, b, c = h
    for d in (4, 3):  # x^3 = -a x^2 - b x - c
        t = r[d]; r[d] = 0
        r[d-1] -= a*t; r[d-2] -= b*t; r[d-3] -= c*t
    return [x % q for x in r[:3]]
def pw(u, e):
    r = [1, 0, 0]
    while e:
        if e & 1: r = mul(r, u)
        u = mul(u, u); e >>= 1
    return r
Q3 = q**3 - 1; o = q*q + q + 1
def order(u):
    f = Q3; e = Q3
    for pr in set(p for p in range(2, Q3+1) if Q3 % p == 0 and all(p % t for t in range(2, int(p**.5)+1))):
        while e % pr == 0 and pw(u, e // pr) == [1, 0, 0]: e //= pr
    return e
gen = next(u for u in ([a, b, c] for a in range(q) for b in range(q) for c in range(q)) if any(u) and order(u) == Q3)
theta = pw(gen, q - 1)   # order q^2+q+1, norm 1
k = o
if (q - 1) % 3 == 0: theta = pw(theta, 3); k = o // 3   # avoid the scalar of order 3 (it has fixed points)
M = np.array([mul(theta, [1 if i == j else 0 for i in range(3)]) for j in range(3)]).T % q  # columns = theta * basis_j
det = int(round(np.linalg.det(M))) % q
assert det == 1, det
Minv = np.array([[0]*3]*3)
# inverse mod q via adjugate
A = M.astype(object)
adj = [[(A[(j+1)%3][(i+1)%3]*A[(j+2)%3][(i+2)%3] - A[(j+1)%3][(i+2)%3]*A[(j+2)%3][(i+1)%3]) for j in range(3)] for i in range(3)]
Minv = np.array(adj, dtype=np.int64) % q
assert ((M @ Minv) % q == np.eye(3, dtype=np.int64)).all()
MiT = Minv.T
key = {tuple(c): i for i, c in enumerate(coord)}
def norm(v):
    for x in v:
        if x % q:
            iv = pow(int(x), q - 2, q); return tuple(int(y) * iv % q for y in v)
X = coord.copy()
gx = (X[:, 0:3] @ M.T) % q; gy = (X[:, 4:7] @ MiT.T) % q
img = np.concatenate([gx, X[:, 3:4], gy], axis=1)
pp = np.array([key[norm(r)] for r in img], dtype=np.int32)
lkey = {tuple(sorted(l)): i for i, l in enumerate(lines)}
lp = np.array([lkey[tuple(sorted(pp[l]))] for l in lines], dtype=np.int32)
# order and freeness
cur = np.arange(N); cl = np.arange(N); fixed = 0
for e in range(1, k + 1):
    cur = pp[cur]; cl = lp[cl]
    if e < k: fixed += int((cur == np.arange(N)).sum() + (cl == np.arange(N)).sum())
assert (cur == np.arange(N)).all() and (cl == np.arange(N)).all()
print(f"q={q} torus order {k}, nontrivial powers fix {fixed} points/lines in total (0 = semiregular), orbits {N//k}+{N//k}")
with open(out, 'wb') as f:
    f.write(np.array([N, k], dtype=np.int32).tobytes()); f.write(pp.tobytes()); f.write(lp.tobytes())
