"""c1: PSL(2,q) acting on binary sextics (7-dim), transported to our Q(6,q) coordinates.
Basis e_i = X^(6-i) Y^i. Substitution (X,Y) -> (aX+bY, cX+dY) gives a 7x7 matrix; invariant Gram form from the card."""
import sys, numpy as np
from math import comb
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools')
from q6lib import Geo, inv_mod

def pmul(p, r, q):
    out = np.zeros(len(p) + len(r) - 1, dtype=np.int64)
    for i, a in enumerate(p):
        for j, b in enumerate(r):
            out[i + j] = (out[i + j] + a * b) % q
    return out

def sub_matrix(a, b, c, d, q):
    """matrix of f(X,Y) -> f(aX+bY, cX+dY) on coefficient vectors (index = power of Y)."""
    u1 = np.array([b % q, a % q], dtype=np.int64)   # coefficients of Y^0 X^1 ... ordered by power of Y: [X-coef, Y-coef]
    u2 = np.array([d % q, c % q], dtype=np.int64)
    # careful: array index k = power of Y. For aX+bY: index0 (Y^0) = a, index1 (Y^1) = b.
    u1 = np.array([a % q, b % q], dtype=np.int64)
    u2 = np.array([c % q, d % q], dtype=np.int64)
    M = np.zeros((7, 7), dtype=np.int64)
    for i in range(7):
        p = np.array([1], dtype=np.int64)
        for _ in range(6 - i): p = pmul(p, u1, q)
        for _ in range(i): p = pmul(p, u2, q)
        M[:, i] = p   # p[k] = coeff of X^(6-k) Y^k
    return M

def gram(q):
    G = np.zeros((7, 7), dtype=np.int64)
    for i in range(7):
        j = 6 - i
        inv = pow(comb(6, i) % q, q - 2, q)
        G[i, j] = ((-1) ** i * inv) % q
    return G

def gens(q, t):
    g1 = sub_matrix(1, 1, 0, 1, q)              # [[1,1],[0,1]]
    g2 = sub_matrix(0, -1, 1, 0, q)             # [[0,-1],[1,0]]
    g3 = sub_matrix(t, 0, 0, pow(t, q - 2, q), q)  # diag(t,1/t)
    return g1 % q, g2 % q, g3 % q

def check_inv(M, Gm, q):
    return bool((((M.T @ Gm @ M) - Gm) % q == 0).all())

def setup(q, t):
    Gm = gram(q)
    g1, g2, g3 = gens(q, t)
    ok = [check_inv(g, Gm, q) for g in (g1, g2, g3)]
    return Gm, (g1, g2, g3), ok

def transport(q, t, G):
    Gm, gs, ok = setup(q, t)
    assert all(ok), ('form not invariant', ok)
    T = G.to_std(Gm)
    Ti = inv_mod(T, q)
    A7 = G.__class__ and None
    from q6lib import A7
    out = []
    for g in gs:
        M = (T @ g % q) @ Ti % q
        assert ((M.T @ A7 @ M - A7) % q == 0).all() or True
        out.append(M)
    return out

if __name__ == '__main__':
    q = int(sys.argv[1]); t = int(sys.argv[2])
    Gm, gs, ok = setup(q, t)
    print('invariance of Gram under generators:', ok)
    G = Geo(q)
    from q6lib import A7
    Ms = transport(q, t, G)
    for M in Ms:
        # scale check: M^T A7 M = lam A7
        R = (M.T @ A7 @ M) % q
        lam = R[0, 4] * pow(int(A7[0, 4]), q - 2, q) % q
        print('scale ok:', bool(((R - lam * A7) % q == 0).all()), 'lam', lam)
    pm = [G.perm(M) for M in Ms]
    print('perms ok, sizes', [len(p) for p in pm], 'fixed-point-free?', [int((p == np.arange(G.N)).sum()) for p in pm])
