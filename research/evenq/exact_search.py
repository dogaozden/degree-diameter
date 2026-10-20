"""Search span(affine basis) for (nu, h) and l(z) = c0 a + c1 b such that at every free point p the slope of
nu(X_p(z)) + h(z) + l(z) along A_p is nonzero; then W = {m in S_z : nu(X(m)) + h(z) + l(z) = 0} is exact.
Every hit is re-verified directly (each free point on exactly one line of W).

python3 exact_search.py q [MAXCOMBOS] [SEED]
"""
import itertools
import json
import sys

import numpy as np

import affine as A

q = int(sys.argv[1])
maxc = int(sys.argv[2]) if len(sys.argv) > 2 else 10**6
seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
A.setup(q, 'lines')
F = A.F
ADD, MUL = F.ADD, F.MUL
basis = np.load(f'runs/affine_basis_q{q}_lines.npy')
free = [int(p) for p in A.Fr.free]
# per free point: (k0, z0, k1, z1) for t = 0, 1 and (p2, p5)
T0 = np.array([[A.params[p][0][0][0], A.params[p][0][0][1], A.params[p][0][1][0], A.params[p][0][1][1]] for p in free])
D = np.array([A.params[p][1] for p in free])  # (p2, p5)
nk = A.nk


def slope(y):
    nu, h = y[:nk], y[nk:]
    f0 = ADD[nu[T0[:, 0]], h[T0[:, 1]]]
    f1 = ADD[nu[T0[:, 2]], h[T0[:, 3]]]
    return ADD[f0, f1]


def combos():
    rng = np.random.default_rng(seed)
    dim = len(basis)
    total = q ** dim
    if total <= maxc:
        for co in itertools.product(range(q), repeat=dim):
            yield np.array(co)
    else:
        for _ in range(maxc):
            yield rng.integers(0, q, dim)


def comb(co):
    y = np.zeros(basis.shape[1], np.int64)
    for c, b in zip(co, basis):
        if c:
            y = ADD[y, MUL[c, b]]
    return y


def verify(y, c0, c1):
    nu, h = y[:nk], y[nk:]
    W = []
    for m, (a, b) in A.zof.items():
        X = [x for x in A.lines[m] if A.Fr.inPi[x]][0]
        val = ADD[ADD[nu[A.kidx[int(A.Fr.Sline_of[X])]], h[A.zidx[(a, b)]]], ADD[MUL[c0, a], MUL[c1, b]]]
        if val == 0:
            W.append(m)
    cov = np.zeros(A.N, int)
    for m in W:
        cov[A.lines[m]] += 1
    return W, bool(np.all(cov[A.Fr.free] == 1))


hits = 0
for co in combos():
    y = comb(co)
    if len(set(y[:nk].tolist())) == 1:
        continue
    s = slope(y)
    for c0 in range(q):
        for c1 in range(q):
            lin = ADD[MUL[c0, D[:, 1]], MUL[c1, D[:, 0]]]  # l along direction (p5, p2)
            if np.all(ADD[s, lin] != 0):
                W, ok = verify(y, c0, c1)
                print('hit: coeffs', co.tolist(), 'c0,c1', c0, c1, '|W|', len(W), 'exact', ok, flush=True)
                if ok and hits == 0:
                    json.dump({'q': q, 'delta': A.Fr.delta, 'v': A.Fr.v, 'S': A.Fr.S.tolist(), 'whiskers': sorted(W),
                               'nu': y[:nk].tolist(), 'h': y[nk:].tolist(), 'zs': A.zs, 'c0c1': [c0, c1]},
                              open(f'whiskers_rule_q{q}.json', 'w'))
                hits += 1
                if hits >= 5:
                    sys.exit(0)
print('hits', hits)
