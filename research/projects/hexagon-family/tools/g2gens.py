"""Root elements of G2(q) acting on H(q) in our coordinates (hexgen2 / q6lib), q odd (prime or 9, 25, 27).
Patterns from research/p4/hats/g2_gens.py (I + N + N^2/2, N a combination of 2 (long) or 4 (short) matrix units);
coefficients re-fitted here against the line set. Also SL3(q) acting as M + 1 + M^-T.
    from g2gens import root_elements; R = root_elements(G)  -> list of (name, 7x7 matrix over GF(q))
Every returned matrix is checked to map lines of H(q) onto lines."""
import itertools, numpy as np
LONG = [((0, 1), (5, 4)), ((0, 2), (6, 4)), ((1, 0), (4, 5)), ((1, 2), (6, 5)), ((2, 0), (4, 6)), ((2, 1), (5, 6))]
SHORT = [((0, 3), (3, 4), (5, 2), (6, 1)), ((0, 5), (1, 4), (3, 2), (6, 3)), ((0, 6), (2, 4), (3, 1), (5, 3)),
         ((1, 3), (3, 5), (4, 2), (6, 0)), ((1, 6), (2, 5), (3, 0), (4, 3)), ((2, 3), (3, 6), (4, 1), (5, 0))]

def _mat(G, units, coefs):
    q = G.q; N = np.zeros((7, 7), dtype=np.int64)
    for (i, j), c in zip(units, coefs): N[i, j] = c
    I = np.eye(7, dtype=np.int64)
    N2 = G.matmul(N, N)
    inv2 = int(np.nonzero(G.MUL[G.fadd(1, 1)] == 1)[0][0])
    half = G.matmul(N2, np.eye(7, dtype=np.int64) * inv2) if not G.prime else (N2 * inv2) % q
    if G.prime: return (I + N + half) % q
    return G.ADD[G.ADD[I, N], half]

def _lines_ok(G, M, lineset, sample=None):
    pm = G.perm(M)
    rows = G.LP if sample is None else G.LP[:sample]
    return all(tuple(sorted(pm[r].tolist())) in lineset for r in rows), pm

def root_elements(G, full_check=True):
    q = G.q; lineset = set(tuple(sorted(r)) for r in G.LP.tolist()); out = []
    for k, pat in enumerate(LONG + SHORT):
        found = None
        for rest in itertools.product(range(1, q), repeat=len(pat) - 1):
            M = _mat(G, pat, (1,) + rest)
            try:
                ok, pm = _lines_ok(G, M, lineset, sample=300)
            except ValueError:
                continue
            if ok and (not full_check or _lines_ok(G, M, lineset)[0]):
                found = M; break
        out.append((('long%d' % k) if k < 6 else ('short%d' % (k - 6)), found))
    return out

def sl3(G, M3):
    """SL3(q) element M3 (3x3, det 1) acting as M3 on (x0,x1,x2), 1 on x3, M3^-T on (x4,x5,x6) (prime q)"""
    from q6lib import inv_mod
    q = G.q; T = np.zeros((7, 7), dtype=np.int64); T[np.ix_([0, 1, 2], [0, 1, 2])] = M3
    T[np.ix_([4, 5, 6], [4, 5, 6])] = inv_mod(M3, q).T; T[3, 3] = 1; return T % q
