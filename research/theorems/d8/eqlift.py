"""Equivariant lifts of H(q) + 2 hop matchings under a cyclic collineation group C (generalizes squad r3-d8/c8 zlift.py).

C = <h>, h a power of g = block(A), A a Singer-type element of SL(3,q) (A on coordinates 0-2, A^-T on 4-6, 1 on 3;
these preserve H(q) in the hexq.py model).  h is chosen semiregular on points and lines.  The hops are C-equivariant
and go from a point to a line at distance 5.  The lift of H(q) + hops by Z_M that commutes with C is the
C x Z_M lift of the quotient base (2N/|C| vertices): edge (orbit i, orbit j) gets voltage (a, b), a = C-offset fixed by
the geometry, b in Z_M free (random here).  Output: liftdiam base "NB |C| M E" + "u v a b".

usage: eqlift.py q order M seed out.txt [holo=1|0] [hopdist=5|any] [singer|g2]
  order: the order of h (must divide q^2+q+1 and give a semiregular action; checked).
"""
import sys
import random
import numpy as np

sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')
import gh  # noqa: E402

q, order, M, seed, OUT = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
HOLO = int(sys.argv[6]) if len(sys.argv) > 6 else 1
HOPD = sys.argv[7] if len(sys.argv) > 7 else '5'
rng = random.Random(seed)
H = gh.load(q)
N = H.N
F = H.F
ADD, MUL, NEG, INV = F.ADD, F.MUL, F.NEG, F.INV
P = np.array(H.P, dtype=np.int64)
POW = q ** np.arange(7, dtype=np.int64)
LINES = np.array(H.lines, dtype=np.int64)
THR = np.array(H.through, dtype=np.int64)


def normalize(V):
    first = np.argmax(V != 0, axis=1)
    lead = V[np.arange(len(V)), first]
    return MUL[V, INV[lead][:, None]]


codes = normalize(P) @ POW
code2idx = {int(c): i for i, c in enumerate(codes)}
lkey = {tuple(sorted(int(p) for p in LINES[k])): k for k in range(N)}


def mmul(A, B):
    n, m, r = A.shape[0], B.shape[1], A.shape[1]
    C = np.zeros((n, m), dtype=np.int64)
    for k in range(r):
        C = ADD[C, MUL[A[:, k][:, None], B[k, :][None, :]]]
    return C


def det3(a):
    t1 = MUL[a[0, 0], ADD[MUL[a[1, 1], a[2, 2]], NEG[MUL[a[1, 2], a[2, 1]]]]]
    t2 = MUL[a[0, 1], ADD[MUL[a[1, 0], a[2, 2]], NEG[MUL[a[1, 2], a[2, 0]]]]]
    t3 = MUL[a[0, 2], ADD[MUL[a[1, 0], a[2, 1]], NEG[MUL[a[1, 1], a[2, 0]]]]]
    return int(ADD[ADD[t1, NEG[t2]], t3])


def inv_T3(a):
    di = INV[det3(a)]
    adj = np.zeros((3, 3), dtype=np.int64)
    for i in range(3):
        for j in range(3):
            r = [x for x in range(3) if x != j]
            c = [x for x in range(3) if x != i]
            m = ADD[MUL[a[r[0], c[0]], a[r[1], c[1]]], NEG[MUL[a[r[0], c[1]], a[r[1], c[0]]]]]
            adj[i, j] = NEG[m] if (i + j) % 2 else m
    return MUL[adj, di].T


def block(A):
    G = np.zeros((7, 7), dtype=np.int64)
    G[0:3, 0:3] = A
    G[4:7, 4:7] = inv_T3(A)
    G[3, 3] = 1
    return G


I7 = np.eye(7, dtype=np.int64)


def mat_order(G, cap):
    X = G.copy()
    for k in range(1, cap + 1):
        if np.array_equal(X, I7):
            return k
        X = mmul(X, G)
    return -1


def mpow(G, k):
    R = I7.copy()
    for _ in range(k):
        R = mmul(R, G)
    return R


GEN = sys.argv[8] if len(sys.argv) > 8 else 'singer'


def el_int(v):
    v %= F.p
    r = 0
    for _ in range(v):
        r = int(ADD[r, 1])
    return r


def root_elt(rot):
    """short-root element of G_2(q) in this model (found by g2gens.py; f = -1), t = 1"""
    G = I7.copy()
    a, b, c = rot, (rot + 1) % 3, (rot + 2) % 3
    G[a, 3] = el_int(2)
    G[a, 4 + a] = 1
    G[3, 4 + a] = 1
    G[4 + b, c] = el_int(-1)
    G[4 + c, b] = 1
    return G


def rand_sl3():
    while True:
        A = np.array([[rng.randrange(q) for _ in range(3)] for _ in range(3)], dtype=np.int64)
        if det3(A) == 1:
            return block(A)


if GEN == 'singer':
    target = q * q + q + 1
    while True:
        A = np.array([[rng.randrange(q) for _ in range(3)] for _ in range(3)], dtype=np.int64)
        if det3(A) != 1:
            continue
        if mat_order(block(A), target + 1) == target:
            break
    assert target % order == 0
    h = mpow(block(A), target // order)
else:  # random element of G_2(q) whose order is a multiple of `order`, then the power of order `order`
    gens = [root_elt(r) for r in range(3)]
    for _ in range(4000):
        g = I7.copy()
        for _ in range(12):
            g = mmul(g, gens[rng.randrange(3)] if rng.random() < 0.5 else rand_sl3())
        o = mat_order(g, 4 * q ** 3)
        if o > 0 and o % order == 0:
            h = mpow(g, o // order)
            break
    else:
        raise RuntimeError('no element of the requested order found')


def perm_pts(G):
    Y = mmul(P, G.T)  # row vectors: x -> G x
    return np.array([code2idx[int(c)] for c in normalize(Y) @ POW])


hp = perm_pts(h)
hl = np.array([lkey[tuple(sorted(int(hp[p]) for p in LINES[k]))] for k in range(N)])
# semiregularity: h^k has no fixed point / line for 0 < k < order
cp, cl = np.arange(N), np.arange(N)
for k in range(1, order):
    cp, cl = hp[cp], hl[cl]
    assert not np.any(cp == np.arange(N)) and not np.any(cl == np.arange(N)), f'h^{k} has fixed elements'
cp, cl = hp[cp], hl[cl]
assert np.array_equal(cp, np.arange(N)) and np.array_equal(cl, np.arange(N))


def orbits(perm):
    rep = -np.ones(N, dtype=np.int64)
    off = np.zeros(N, dtype=np.int64)
    reps = []
    for x0 in range(N):
        if rep[x0] >= 0:
            continue
        j = len(reps)
        reps.append(x0)
        y = x0
        for a in range(order):
            rep[y], off[y] = j, a
            y = perm[y]
    return rep, off, reps


prep, poff, preps = orbits(hp)
lrep, loff, lreps = orbits(hl)
NO = len(preps)
assert NO == len(lreps) == N // order
# powers of hl on line ids: hlpow[a][k] = h^a(k)
hlpow = np.zeros((order, N), dtype=np.int64)
hlpow[0] = np.arange(N)
for a in range(1, order):
    hlpow[a] = hl[hlpow[a - 1]]


def near_lines(x):
    """lines at distance <= 3 from point x"""
    col = np.unique(LINES[THR[x]].ravel())  # points collinear with x (incl. x)
    return set(np.unique(THR[col].ravel()).tolist())


NEAR = [near_lines(preps[i]) for i in range(NO)]


def build_matching(other=None):
    for _ in range(1000):
        sigma = list(range(NO))
        rng.shuffle(sigma)
        cs = []
        ok = True
        for i in range(NO):
            opts = []
            for c in range(order):
                L = int(hlpow[c][lreps[sigma[i]]])
                if HOPD == '5' and L in NEAR[i]:
                    continue
                if L in THR[preps[i]]:
                    continue
                if other is not None and other[preps[i]] == L:
                    continue
                opts.append(c)
            if not opts:
                ok = False
                break
            cs.append(rng.choice(opts))
        if ok:
            return sigma, cs
    raise RuntimeError('no equivariant matching found')


def targets(sigma, cs):
    t = np.zeros(N, dtype=np.int64)
    for x in range(N):
        i, a = prep[x], poff[x]
        t[x] = hlpow[(cs[i] + a) % order][lreps[sigma[i]]]
    return t


s1, c1 = build_matching()
t1 = targets(s1, c1)
s2, c2 = build_matching(t1)
t2 = targets(s2, c2)
assert len(set(t1.tolist())) == N and len(set(t2.tolist())) == N and np.all(t1 != t2)
edges = []
for i in range(NO):
    x0 = preps[i]
    for k in list(THR[x0]) + [int(t1[x0]), int(t2[x0])]:
        edges.append((i, NO + int(lrep[k]), int(loff[k])))
with open(OUT, 'w') as fh:
    fh.write(f'{2 * NO} {order} {M} {len(edges)}\n')
    for e, (u, v, a) in enumerate(edges):
        is_flag = (e % (q + 3)) < q + 1
        b = rng.randrange(M) if (HOLO or not is_flag) else 0
        fh.write(f'{u} {v} {a} {b}\n')
print(f'q {q} |C| {order} orbits {NO} base {2 * NO} edges {len(edges)} M {M} -> {OUT}', flush=True)
