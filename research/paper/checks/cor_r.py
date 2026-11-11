# Spot check of Corollary 6.23 of joint.tex at q = 5, r = 2, built from the paper's recipe:
# R = q^2+1 points of an elliptic quadric section, R* = q^2+1 lines of a Hermitian spread, sigma as in Prop. 6.17,
# 2r+1 = 5 levels of type H, M_t = sigma and R_t = R on every transition, K = min(r(q^2+1), kappa(q-r)) = 7 hubs per colour,
# hub graph = incidence graph of PG(2,2) (Lemma 6.19 with s = 2, no pendant vertices). Writes an edge list for apsp.c.
import itertools, random, sys
q, r = 5, 2
inv = lambda x: pow(x % q, q - 2, q)
def norm(v):
    for x in v:
        if x % q:
            i = inv(x); return tuple(y * i % q for y in v)
Q = lambda X: (X[0]*X[4] + X[1]*X[5] + X[2]*X[6] - X[3]*X[3]) % q
b = lambda X, Y: (Q([x + y for x, y in zip(X, Y)]) - Q(X) - Q(Y)) % q
pts = sorted({norm(v) for v in itertools.product(range(q), repeat=7) if any(v) and Q(v) == 0})
N = len(pts)
def tits(x, y):
    p = lambda i, j: (x[i]*y[j] - x[j]*y[i]) % q
    return (p(1,2) == p(3,4) and p(5,4) == p(3,2) and p(2,0) == p(3,5) and p(6,5) == p(3,0) and p(0,1) == p(3,6) and p(4,6) == p(3,1))
lines = set()
for i, x in enumerate(pts):
    for y in pts[i+1:]:
        if b(x, y) == 0 and tits(x, y):
            lines.add(frozenset(norm([(s*xx + t*yy) % q for xx, yy in zip(x, y)]) for s in range(q) for t in range(q) if (s, t) != (0, 0)))
lines = sorted(lines, key=lambda L: sorted(L)); assert len(lines) == N
pid = {p: i for i, p in enumerate(pts)}
on = [[] for _ in pts]
for j, L in enumerate(lines):
    for p in L: on[pid[p]].append(j)
lp = [[pid[p] for p in L] for L in lines]
# incidence graph I: points 0..N-1, lines N..2N-1
def nbrs(x):
    return [N + j for j in on[x]] if x < N else lp[x - N]
# R: points of Q(6,5) in span(e0, e4, e3, e1 + 2 e5)  (2 is a non-square mod 5)
lam = 2
R = []
for a0, a4, a3, t in itertools.product(range(q), repeat=4):
    if (a0, a4, a3, t) == (0, 0, 0, 0): continue
    X = [a0, t, 0, a3, a4, lam * t % q, 0]
    if Q(X) == 0: R.append(pid[norm(X)])
R = sorted(set(R)); assert len(R) == q*q + 1, len(R)
# R*: q^2+1 lines of the Hermitian spread in X0 + 2 X4 = 0
c = 2
S = [j for j, L in enumerate(lines) if all((p[0] + c*p[4]) % q == 0 for p in L)]
assert len(S) == q**3 + 1
Rstar = S[:q*q + 1]
# distance-2 sets
def gamma2(x):
    out = set()
    for y in nbrs(x):
        for z in nbrs(y):
            if z != x: out.add(z)
    return out
# sigma: points -> lines (vertex ids N..2N-1), as in Prop 6.17
sigma = {}
used = set()
for x, L in zip(R, Rstar):
    sigma[x] = N + L; used.add(N + L)
for x in R:
    A = sorted(gamma2(x)); B = sorted(gamma2(sigma[x]))
    assert len(A) == len(B) == q*(q+1)
    for a, bb in zip(A, B):
        assert a not in sigma and bb not in used
        sigma[a] = bb; used.add(bb)
rest_p = [x for x in range(N) if x not in sigma]
rest_l = [N + j for j in range(N) if N + j not in used]
random.seed(1); random.shuffle(rest_l)
for a, bb in zip(rest_p, rest_l): sigma[a] = bb
assert len(sigma) == N and len(set(sigma.values())) == N
# (H1)-(H3) at every x in R
Rs = set(R)
for x in R:
    assert not (gamma2(x) & Rs)
    assert {sigma[z] for z in gamma2(x)} == gamma2(sigma[x])
# level graph, 5 levels, edges
L5 = 2*r + 1
vid = lambda x, j: j * 2 * N + x
E = []
for j in range(L5):
    for x in range(N):
        for y in nbrs(x):
            if x < y: E.append((vid(x, j), vid(y, j)))
    for k in range(1, r + 1):
        for x in range(N):
            if x in Rs: continue  # freed
            E.append((vid(x, j), vid(sigma[x], (j + k) % L5)))
# hubs: K = 7 per colour; B-hub i joined to (R[i], j) in every level, A-hub i to (sigma(R[i]), j)
K = 7
nlev = L5 * 2 * N
Bh = lambda i: nlev + i; Ah = lambda i: nlev + K + i
for i in range(K):
    for j in range(L5):
        E.append((Bh(i), vid(R[i], j))); E.append((Ah(i), vid(sigma[R[i]], j)))
# hub graph: incidence graph of PG(2,2): points = B-hubs, lines = A-hubs
fano = [(0,1,3),(1,2,4),(2,3,5),(3,4,6),(4,5,0),(5,6,1),(6,0,2)]
for li, Lf in enumerate(fano):
    for pi in Lf: E.append((Bh(pi), Ah(li)))
n = nlev + 2*K
assert n == 10 * N + 14
with open(sys.argv[1], 'w') as f:
    f.write(f"{n}\n")
    for u, w in E: f.write(f"{u} {w}\n")
print("wrote", n, "vertices", len(E), "edges")
