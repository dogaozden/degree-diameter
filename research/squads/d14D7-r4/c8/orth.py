#!/usr/bin/env python3
# c3 (round 3): cyclic symmetry of partial ovoids of E = Q^-(5,11), from O^-(6,11) acting on V = {x4 = -x0}.
# Coordinates of V: u = (x0,x1,x2,x3,x5,x6); B(u,w) = u^T M w, Q(u) = B(u,u)/2 (same B as spreadpack.c / pack rules).
# Usage (as module): see main() at the bottom for the sampling / orbit search.
import numpy as np, sys, time, math, json
p = 11
D = '/home/user/degree-diameter/research/cell147/data/'
rows = np.loadtxt(D + 'E11.map', dtype=np.int64)
pid = rows[:, 0].copy(); sline = rows[:, 1].copy()
X = rows[:, 2:9] % p
N = X.shape[0]
assert np.all(X[:, 4] == (-X[:, 0]) % p)
U = X[:, [0, 1, 2, 3, 5, 6]].copy()
Qv = (-U[:, 0] ** 2 + U[:, 1] * U[:, 4] + U[:, 2] * U[:, 5] - U[:, 3] ** 2) % p
assert np.all(Qv == 0)
M = np.zeros((6, 6), dtype=np.int64)
M[0, 0] = -2 % p; M[1, 4] = M[4, 1] = 1; M[2, 5] = M[5, 2] = 1; M[3, 3] = -2 % p
INV = np.array([0] + [pow(a, p - 2, p) for a in range(1, p)], dtype=np.int64)
PW = np.array([p ** i for i in range(6)], dtype=np.int64)
IDX = np.full(p ** 6, -1, dtype=np.int64); IDX[U @ PW] = np.arange(N)
assert np.all(IDX[U @ PW] == np.arange(N))

def normalize(A):
    A = A % p
    first = np.argmax(A != 0, axis=1)
    lead = A[np.arange(A.shape[0]), first]
    return (A * INV[lead][:, None]) % p

def perm_of(g):
    """permutation of the points of E induced by u -> g u (g: 6x6 over F_11, must preserve M)."""
    IM = normalize((U @ g.T) % p)
    perm = IDX[IM @ PW]
    assert np.all(perm >= 0), "image not on E"
    return perm

def Bm(a, b):
    return (a @ M @ b.T) % p

def refl(v):
    Mv = (M @ v) % p
    q = int((v @ Mv) % p) * 6 % p          # Q(v) = B(v,v)/2, 1/2 = 6 mod 11
    assert q != 0
    return (np.eye(6, dtype=np.int64) - np.outer(v, Mv) * INV[q]) % p

def rand_elem(rng, k):
    g = np.eye(6, dtype=np.int64)
    for _ in range(k):
        while True:
            v = rng.integers(0, p, 6).astype(np.int64)
            if int((v @ M @ v) % p) != 0: break
        g = (g @ refl(v)) % p
    return g

def cycles(perm):
    seen = np.zeros(N, dtype=bool); out = []
    pl = perm.tolist()
    for i in range(N):
        if seen[i]: continue
        c = []; j = i
        while not seen[j]:
            seen[j] = True; c.append(j); j = pl[j]
        out.append(c)
    return out

def lcm(a, b): return a * b // math.gcd(a, b)

def pperm(perm, k):
    res = np.arange(N); base = perm.copy()
    while k:
        if k & 1: res = base[res]
        base = base[base]; k >>= 1
    return res

def indep_orbits(cyc):
    """orbits (cycles) that are independent sets; returns list of (index, rep, orbit list)."""
    out = []
    for oi, c in enumerate(cyc):
        if len(c) == 1: out.append(oi); continue
        b = Bm(U[c[0]:c[0] + 1], U[c])[0]
        if np.all(b[1:] != 0): out.append(oi)
    return out

def compat_matrix(cyc, ind):
    """compat[a,b] (a,b indices into ind): True iff every point of orbit ind[a] is non-orthogonal to every point of ind[b]."""
    if len(ind) == 0: return np.zeros((0, 0), dtype=bool)
    reps = np.array([cyc[o][0] for o in ind], dtype=np.int64)
    Z = (Bm(U[reps], U) == 0)                       # (nind, N): orthogonal to rep
    oid = np.empty(N, dtype=np.int64); sizes = []
    order = []
    for oi, c in enumerate(cyc):
        order.extend(c); sizes.append(len(c))
    order = np.array(order); starts = np.concatenate([[0], np.cumsum(sizes)[:-1]])
    cnt = np.add.reduceat(Z[:, order], starts, axis=1)  # (nind, norb)
    comp = (cnt[:, ind] == 0)
    return comp

def max_wclique(adj, w, tlimit=20.0):
    """exact weighted max clique by branch and bound; adj: list of int bitsets; w: weights."""
    n = len(w); best = [0, []]; t0 = time.time(); stop = [False]
    def bits(x):
        while x:
            lb = x & -x; yield lb.bit_length() - 1; x ^= lb
    def expand(R, Rw, cand):
        if Rw > best[0]: best[0] = Rw; best[1] = list(R)
        if stop[0]: return
        if time.time() - t0 > tlimit: stop[0] = True; return
        while cand:
            if Rw + sum(w[i] for i in bits(cand)) <= best[0]: return
            lb = cand & -cand; i = lb.bit_length() - 1; cand ^= lb
            expand(R + [i], Rw + w[i], cand & adj[i])
    expand([], 0, (1 << n) - 1)
    return best[0], best[1], not stop[0]

def flags_of(S, path):
    with open(path, 'w') as f:
        for i in S: f.write(f"{pid[i]} {sline[i]}\n")

def is_indep(S):
    S = list(S)
    if len(S) < 2: return True
    b = Bm(U[S], U[S]); np.fill_diagonal(b, 1)
    return bool(np.all(b != 0))

if __name__ == '__main__':
    # sanity: M preserved by a random element
    rng = np.random.default_rng(1)
    g = rand_elem(rng, 6)
    assert np.all((g.T @ M @ g) % p == M), "not an isometry"
    perm = perm_of(g)
    print("N", N, "sanity ok; perm of random element built")
