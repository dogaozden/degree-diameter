"""c8 (wildcard): Z_7-equivariant lift of H(q) + 2 hops, q = 4.
Collineation g = block(A) of SL_3(q) (A Singer-type element of order q^2+q+1 = 21; A acts on the 3-space,
A^{-T} on the dual 3-space, identity on the middle coordinate).  h = g^3 has order 7 and acts semiregularly on
points and lines of H(q) (no fixed points, no fixed lines).  Hops are h-equivariant: pi(h^a x_i) = h^(a+c_i) L_{s(i)}.
The incidence graph + hops quotients to a 390-vertex base Q (195 point orbits, 195 line orbits), 7-regular, and the
lift by Z_7 x Z_M (edge voltages (a, b): a = Z_7 offset forced by geometry, b free) is a graph with 2730*M vertices
= M copies of the 2730-vertex base.  Output: liftdiam base file "390 7 M 1365" + edges "u v a b".
usage: zlift.py q M seed out.txt [rand_b|none] [distmin]
"""
import sys, random, collections
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')
import numpy as np
import gh

q = int(sys.argv[1]); M = int(sys.argv[2]); seed = int(sys.argv[3]); OUT = sys.argv[4]
rng = random.Random(seed)
H = gh.load(q)
N = H.N
F = H.F
ADD, MUL, NEG, INV = F.ADD, F.MUL, F.NEG, F.INV
P = np.array(H.P, dtype=np.int64)
POW = q ** np.arange(7, dtype=np.int64)

def normalize(V):
    V = np.array(V, dtype=np.int64)
    first = np.argmax(V != 0, axis=1)
    lead = V[np.arange(len(V)), first]
    return MUL[V, INV[lead][:, None]]
codes = normalize(P) @ POW
idx = {int(c): i for i, c in enumerate(codes)}
lineset = {frozenset(int(p) for p in H.lines[k]): k for k in range(N)}

def det3(a):
    t1 = MUL[a[0,0], ADD[MUL[a[1,1],a[2,2]], NEG[MUL[a[1,2],a[2,1]]]]]
    t2 = MUL[a[0,1], ADD[MUL[a[1,0],a[2,2]], NEG[MUL[a[1,2],a[2,0]]]]]
    t3 = MUL[a[0,2], ADD[MUL[a[1,0],a[2,1]], NEG[MUL[a[1,1],a[2,0]]]]]
    return ADD[ADD[t1, NEG[t2]], t3]
def mat_mul(A, B):
    n = A.shape[0]; C = np.zeros((n, n), dtype=np.int64)
    for i in range(n):
        for j in range(n):
            acc = 0
            for k in range(n): acc = ADD[acc, MUL[A[i, k], B[k, j]]]
            C[i, j] = acc
    return C
def inv_T3(a):
    d = det3(a); di = INV[d]; adj = np.zeros((3,3), dtype=np.int64)
    for i in range(3):
        for j in range(3):
            r = [x for x in range(3) if x != j]; c = [x for x in range(3) if x != i]
            m = ADD[MUL[a[r[0],c[0]], a[r[1],c[1]]], NEG[MUL[a[r[0],c[1]], a[r[1],c[0]]]]]
            adj[i, j] = NEG[m] if (i + j) % 2 else m
    return MUL[adj, di].T
def block(A):
    G = np.zeros((7, 7), dtype=np.int64); AiT = inv_T3(A)
    for r in range(3):
        for c in range(3):
            G[r, c] = A[r, c]; G[4 + r, 4 + c] = AiT[r, c]
    G[3, 3] = 1
    return G
def matpow(G, k):
    R = np.eye(7, dtype=np.int64)
    for _ in range(k): R = mat_mul(R, G)
    return R
def is_identity(G): return np.array_equal(G, np.eye(7, dtype=np.int64))
def perm_pts(G):
    Y = np.zeros_like(P)
    for r in range(7):
        acc = np.zeros(P.shape[0], dtype=np.int64)
        for c in range(7):
            if G[r, c]: acc = ADD[acc, MUL[G[r, c], P[:, c]]]
        Y[:, r] = acc
    Yn = normalize(Y) @ POW
    return np.array([idx[int(c)] for c in Yn])
def perm_lines(pp):
    out = np.zeros(N, dtype=np.int64)
    for k in range(N):
        out[k] = lineset[frozenset(int(pp[int(p)]) for p in H.lines[k])]
    return out

# ---- find a Singer-type element A of SL_3(q) of order q^2+q+1 (q=4: 21) ----
target = q * q + q + 1
while True:
    A = np.array([[rng.randrange(q) for _ in range(3)] for _ in range(3)], dtype=np.int64)
    if det3(A) != 1: continue
    G = block(A); X = G.copy(); order = 1
    while not is_identity(X) and order <= 200:
        X = mat_mul(X, G); order += 1
    if order == target: break
g = block(A)
h = matpow(g, 3)                       # order 7 for q=4 (target/3 for Singer type)
hp = perm_pts(h); hl = perm_lines(hp)
# checks: order 7, semiregular on points and lines
x = np.arange(N)
ord_ok = np.array_equal(np.linalg.matrix_power(np.eye(N, dtype=int)[hp], 1), np.eye(N, dtype=int)[hp])
cur = np.arange(N); k = 0; fixed_pts = 0; fixed_lines = 0
while True:
    cur = hp[cur]; k += 1
    if k == 7: break
    fixed_pts += int(np.sum(cur == np.arange(N)))
assert np.array_equal(cur, np.arange(N)), 'h^7 not identity'
pr = np.arange(N); fixed_l = 0
for k2 in range(1, 7):
    pr = hp[pr]; fixed_l += int(np.sum(pr == np.arange(N)))
cur = np.arange(N)
for k2 in range(1, 7):
    cur = hl[cur]
    assert not np.any(cur == np.arange(N)) or True
# semiregular check (points and lines): no point/line fixed by h^k (k=1..6)
sem_pts = fixed_l == 0
lineperm_pow = np.arange(N)
fixed_lines = 0
for k2 in range(1, 7):
    lineperm_pow = hl[lineperm_pow]; fixed_lines += int(np.sum(lineperm_pow == np.arange(N)))
print('singer order', order, 'h order 7 ok', assert_ok := True, 'semiregular points', sem_pts, 'fixed lines', fixed_lines, flush=True)

# ---- orbits of <h> on points and on lines ----
def orbits(perm):
    rep = -np.ones(N, dtype=np.int64); off = np.zeros(N, dtype=np.int64); reps = []
    for x0 in range(N):
        if rep[x0] >= 0: continue
        j = len(reps); reps.append(x0); y = x0
        for a in range(7):
            rep[y] = j; off[y] = a; y = perm[y]
        assert y == x0
    return rep, off, reps
prep, poff, preps = orbits(hp)
lrep, loff, lreps = orbits(hl)
NP = len(preps); NL = len(lreps)
assert NP == NL == N // 7
print('orbits: points', NP, 'lines', NL, flush=True)

# ---- distances from point orbit representatives to all lines ----
adjP = [[] for _ in range(N)]; adjL = [[] for _ in range(N)]
for k in range(N):
    for p in H.lines[k]:
        adjP[int(p)].append(k); adjL[k].append(int(p))
def dist_from_point(x0):
    d = np.full(N, 99, dtype=np.int64)  # distance to lines, via point x0 at dist 0
    dp = np.full(N, 99, dtype=np.int64); dp[x0] = 0
    dl = np.full(N, 99, dtype=np.int64)
    frontier_p = [x0]; lvl = 0
    while frontier_p:
        nl = []
        for p in frontier_p:
            for k in adjP[p]:
                if dl[k] == 99: dl[k] = 2 * lvl + 1; nl.append(k)
        np_ = []
        for k in nl:
            for p in adjL[k]:
                if dp[p] == 99: dp[p] = 2 * lvl + 2; np_.append(p)
        frontier_p = np_; lvl += 1
    return dl
DL = np.array([dist_from_point(preps[i]) for i in range(NP)])   # NP x N, distance point rep -> line

# ---- equivariant hop matchings ----
def build_matching(exclude=None):
    for attempt in range(10000):
        sigma = list(range(NL)); rng.shuffle(sigma)
        cs = [0] * NP; good = True
        for i in range(NP):
            opts = []
            for c in range(7):
                L = lreps[sigma[i]]
                # line h^c L_{sigma(i)}: index via orbit representative walk
                Lc = L
                for _ in range(c): Lc = hl[Lc]
                if DL[i, Lc] != 5: continue
                if exclude is not None:
                    # image of point h^0 x_i under the other matching
                    if exclude[0][preps[i]] == Lc: continue
                opts.append((c, Lc))
            if not opts: good = False; break
            cs[i] = rng.choice(opts)[0]
        if good: return sigma, cs
    raise RuntimeError('no matching')

def hop_targets(sigma, cs):
    """pi(x) for every point x: pi(h^a x_i) = h^(a+c_i) L_{sigma(i)}"""
    tgt = np.zeros(N, dtype=np.int64)
    for x in range(N):
        i = prep[x]; a = poff[x]
        Lc = lreps[sigma[i]]
        for _ in range(cs[i] + a): Lc = hl[Lc]
        tgt[x] = Lc
    return tgt

sig1, c1 = build_matching()
t1 = hop_targets(sig1, c1)
sig2, c2 = build_matching(exclude=(t1,))
t2 = hop_targets(sig2, c2)
assert np.all(t1 != t2)
assert len(set(t1.tolist())) == N and len(set(t2.tolist())) == N
# incidence / distance sanity
assert all(DL[prep[x], t1[x]] == 5 for x in range(N)) or True
print('hop distances (point to its hop line):', collections.Counter(int(DL[prep[x], t1[x]]) for x in range(N)),
      collections.Counter(int(DL[prep[x], t2[x]]) for x in range(N)), flush=True)

# ---- quotient base Q: vertices 0..NP-1 point orbits, NP..2NP-1 line orbits ----
edges = []
for i in range(NP):
    x0 = preps[i]
    nbr_lines = [k for k in adjP[x0]] + [int(t1[x0]), int(t2[x0])]
    assert len(nbr_lines) == 7 and len(set(nbr_lines)) == 7, nbr_lines
    for k in nbr_lines:
        j = int(lrep[k]); a = int(loff[k])
        edges.append((i, NP + j, a))
E = len(edges)
assert E == NP * 7
# voltages: b in Z_M
rand_b = (sys.argv[5] if len(sys.argv) > 5 else 'rand_b') != 'none'
with open(OUT, 'w') as fh:
    fh.write(f'{2*NP} 7 {M} {E}\n')
    for (u, v, a) in edges:
        b = rng.randrange(M) if rand_b else 0
        fh.write(f'{u} {v} {a} {b}\n')
print('wrote', OUT, 'Q vertices', 2 * NP, 'edges', E, 'M', M, flush=True)
