"""c15: typed-layout slot formulas. For each r (n = 2r+1 levels), search regular tournaments T and typings t
(H=0, D=1); caps H->D = a, D->H = b, H->H and D->D = c.
K_B = min_v (sum of caps of out-arcs of v), K_A = min_v (sum of caps of in-arcs of v).
Each candidate is a pair of min-of-linear-forms, forms (alpha,beta,gamma) with alpha+beta+gamma = r.
Objective is positively homogeneous in (a,b,c), so we evaluate on integer points with a=100 and tabulate formulas."""
import numpy as np, itertools, random, sys, time, json
from collections import defaultdict

def all_regular_small(n):
    r = (n - 1) // 2
    pairs = list(itertools.combinations(range(n), 2)); m = len(pairs)
    bits = np.arange(1 << m, dtype=np.int64)
    od = np.zeros((1 << m, n), dtype=np.int16)
    for i, (u, v) in enumerate(pairs):
        bit = (bits >> i) & 1
        od[:, u] += bit; od[:, v] += 1 - bit
    ok = np.all(od == r, axis=1)
    out = []
    for x in bits[ok]:
        A = np.zeros((n, n), dtype=np.int8)
        for i, (u, v) in enumerate(pairs):
            if (int(x) >> i) & 1: A[u, v] = 1
            else: A[v, u] = 1
        out.append(A)
    return out

def circulant(n):
    r = (n - 1) // 2
    out = []
    for bits in range(1 << r):
        S = [k + 1 if (bits >> k) & 1 == 0 else n - (k + 1) for k in range(r)]  # one of {k, n-k}
        A = np.zeros((n, n), dtype=np.int8)
        for j in range(n):
            for k in S: A[j, (j + k) % n] = 1
        out.append(A)
    return out

def flip_walk(A, steps, rng):
    A = A.copy(); n = A.shape[0]
    for _ in range(steps):
        x, y, z = rng.sample(range(n), 3)
        if A[x, y] and A[y, z] and A[z, x]:
            A[x, y] = A[y, z] = A[z, x] = 0; A[y, x] = A[z, y] = A[x, z] = 1
    return A

def random_regular(n, nsamp, spacing, rng):
    base = circulant(n)[0]
    A = base; out = []
    for _ in range(nsamp):
        A = flip_walk(A, spacing, rng); out.append(A.copy())
    return out

def forms(A, types, r):
    """types: (N,n) with 1 = D, 0 = H. Returns OUT, IN of shape (N,n,3): coefficients of (a,b,c)."""
    Dm = types.astype(np.float32); Hm = 1 - Dm; Af = A.astype(np.float32)
    outA = Hm * (Dm @ Af.T); outB = Dm * (Hm @ Af.T); outC = r - outA - outB
    inA = Dm * (Hm @ Af);    inB = Hm * (Dm @ Af);    inC = r - inA - inB
    OUT = np.stack([outA, outB, outC], -1); IN = np.stack([inA, inB, inC], -1)
    return OUT, IN

def evalP(OUT, IN, P):
    """P (G,3) float32. Returns value (N,G), Kb (N,G), Ka (N,G)."""
    N, n, _ = OUT.shape
    Kb = (OUT.reshape(-1, 3) @ P.T).reshape(N, n, -1).min(axis=1)
    Ka = (IN.reshape(-1, 3) @ P.T).reshape(N, n, -1).min(axis=1)
    return Kb + Ka, Kb, Ka

def run(n, tournaments, P):
    """Returns per grid point: best value, dict formula->(tournament index, typing) over all maximisers (ties included)."""
    r = (n - 1) // 2
    types = ((np.arange(1 << n)[:, None] >> np.arange(n)[None, :]) & 1).astype(np.int8)
    G = P.shape[0]; Pf = P.astype(np.float32)
    best = np.full(G, -1.0); tie = [dict() for _ in range(G)]
    eps = 1e-4
    for tid, A in enumerate(tournaments):
        OUT, IN = forms(A, types, r)
        val, _, _ = evalP(OUT, IN, Pf)
        mx = val.max(axis=0)
        for g in range(G):
            if mx[g] < best[g] - eps: continue
            if mx[g] > best[g] + eps:
                best[g] = mx[g]; tie[g] = {}
            p = P[g].astype(float)
            for ti in np.where(val[:, g] >= best[g] - eps)[0]:
                ob = OUT[ti].astype(float) @ p; ia = IN[ti].astype(float) @ p
                for v in np.where(np.isclose(ob, ob.min()))[0]:
                    for u in np.where(np.isclose(ia, ia.min()))[0]:
                        f = tuple(int(x) for x in (OUT[ti, v] + IN[ti, u]))
                        if f not in tie[g]:
                            tie[g][f] = (tid, ''.join('HD'[x] for x in types[ti]))
    return best, tie


def iso_key(A, rounds=3):
    """Colour-refinement invariant (complete enough to separate the 3 and 15 classes for n = 7, 9 in tests)."""
    A = A.astype(np.int64); n = A.shape[0]
    C = A @ A  # C[v,w] = #x: v->x->w ; the 3-cycles through arc v->w are C[w,v]
    col = [()] * n
    for _ in range(rounds):
        new = []
        for v in range(n):
            outs = tuple(sorted((col[w], int(C[w, v])) for w in range(n) if A[v, w]))
            ins = tuple(sorted((col[w], int(C[v, w])) for w in range(n) if A[w, v]))
            new.append((col[v], outs, ins))
        col = [hash(x) for x in new]
    # 4-vertex profile: for each vertex, multiset of (own score, sorted score vector) over 4-subsets containing it
    import itertools
    prof = [[] for _ in range(n)]
    for Q in itertools.combinations(range(n), 4):
        sc = {x: int(sum(A[x, y] for y in Q)) for x in Q}
        sv = tuple(sorted(sc.values()))
        for x in Q: prof[x].append((sc[x], sv))
    col = [(col[v], tuple(sorted(prof[v]))) for v in range(n)]
    return tuple(sorted(hash(c) for c in col))

def dedupe(T, limit=None):
    seen = {}
    for A in T:
        k = iso_key(A)
        if k not in seen: seen[k] = A
    reps = list(seen.values())
    return reps[:limit] if limit else reps
