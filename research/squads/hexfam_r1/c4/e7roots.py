"""E7 root system mod q inside GF(q)^7 with form A7 (B(v,v)=2 for roots). Simple roots: Bourbaki Dynkin 1-3,3-4,4-5,5-6,6-7,2-4."""
import random, numpy as np
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/hexfam_r1/c4')
from lib import A7

def solve_affine(q, rows, rhs):
    M = [[int(x) % q for x in r] + [int(b) % q] for r, b in zip(rows, rhs)]
    n = 7; piv = []; r = 0
    for c in range(n):
        p = next((i for i in range(r, len(M)) if M[i][c] % q), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        iv = pow(M[r][c], q - 2, q); M[r] = [(x * iv) % q for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % q:
                f = M[i][c]; M[i] = [(x - f * y) % q for x, y in zip(M[i], M[r])]
        piv.append(c); r += 1
    free = [c for c in range(n) if c not in piv]
    part = [0] * n
    for i, c in enumerate(piv): part[c] = M[i][n]
    basis = []
    for f in free:
        v = [0] * n; v[f] = 1
        for i, c in enumerate(piv): v[c] = (-M[i][f]) % q
        basis.append(np.array(v))
    return np.array(part), basis

def find_simple(q, seed):
    Cart = np.zeros((7, 7), dtype=np.int64)
    for i in range(7): Cart[i, i] = 2
    for a, b in [(1, 3), (3, 4), (4, 5), (5, 6), (6, 7), (2, 4)]:
        Cart[a - 1, b - 1] = Cart[b - 1, a - 1] = -1
    rng = random.Random(seed); a = []
    for i in range(7):
        rows = [list((A7 @ a[j]) % q) for j in range(i)]
        rhs = [int(Cart[j, i]) % q for j in range(i)]
        if rows: part, basis = solve_affine(q, rows, rhs)
        else: part, basis = np.zeros(7, dtype=np.int64), [np.eye(7, dtype=np.int64)[k] for k in range(7)]
        for _ in range(20000):
            coef = [rng.randrange(q) for _ in basis]
            v = (part + sum(c * b for c, b in zip(coef, basis))) % q
            if int(v @ A7 @ v) % q == 2 % q:
                a.append(v); break
        else:
            return None
    return np.array(a) % q

def e7_roots(q, seed=1):
    """returns (simple (7,7), roots (126,7)) as exact vectors mod q"""
    for s in range(seed, seed + 500):
        a = find_simple(q, s)
        if a is not None: break
    roots = set(tuple(int(x) for x in v) for v in a) | set(tuple(int(x) for x in (-v) % q) for v in a)
    frontier = list(roots)
    while frontier:
        new = []
        for r in frontier:
            rv = np.array(r)
            for v in a:
                w = (rv - (int(rv @ A7 @ v) % q) * v) % q
                t = tuple(int(x) for x in w)
                if t not in roots: roots.add(t); new.append(t)
        frontier = new
    R = np.array(sorted(roots), dtype=np.int64)
    return a, R

def subsystem(R, q, edges, n, seed=1, tries=300):
    """randomised DFS for vectors b_0..b_{n-1} in R with Gram = Cartan of graph (edges) mod q."""
    adjset = set(map(tuple, edges)) | set((b, a) for a, b in edges)
    rng = random.Random(seed)
    BR = (R @ A7 @ R.T) % q
    target = np.zeros((n, n), dtype=np.int64)
    for i in range(n):
        target[i, i] = 2 % q
        for j in range(n):
            if i != j: target[i, j] = (-1 if (i, j) in adjset else 0) % q
    def dfs(chosen):
        k = len(chosen)
        if k == n: return list(chosen)
        cand = np.ones(len(R), dtype=bool)
        for j, c in enumerate(chosen): cand &= (BR[c] == target[j, k])
        idx = np.nonzero(cand)[0].tolist(); rng.shuffle(idx)
        for c in idx:
            if c in chosen: continue
            res = dfs(chosen + [c])
            if res is not None: return res
        return None
    for t in range(tries):
        c0 = rng.randrange(len(R))
        res = dfs([c0])
        if res is not None: return R[np.array(res)]
    return None
