"""Compatibility graph on cosets of <u> in GF(p)^5 (u = nonsquare direction). Lines L_c = {x(c + lam u)}.
Lines c, c' compatible iff Qp(c - c' + lam u) != 0 for all lam in GF(p) (equivalently B != 0 on all cross pairs).
Reps: vectors with coordinate `piv` (first nonzero coordinate of u) equal to 0. The graph is a Cayley graph on
(Z_p)^4, so it is vertex-transitive: WLOG the clique contains the zero coset."""
import sys, itertools, numpy as np
from hexaffine import nonsquare_direction

def build(p, u=None):
    if u is None:
        u = nonsquare_direction(p)
    piv = next(i for i in range(5) if u[i] % p)
    R = np.array([v for v in itertools.product(range(p), repeat=5) if v[piv] == 0], dtype=np.int16)
    N = len(R)
    D = (R[:, None, :] - R[None, :, :]) % p
    U = np.array(u, dtype=np.int16)
    bad = np.zeros((N, N), dtype=bool)
    for lam in range(p):
        E = (D + lam * U) % p
        val = (E[..., 2] * E[..., 2] - E[..., 0] * E[..., 3] - E[..., 1] * E[..., 4]) % p
        bad |= (val == 0)
    adj = ~bad
    np.fill_diagonal(adj, False)
    assert (adj == adj.T).all()
    return u, R, adj

if __name__ == '__main__':
    p = int(sys.argv[1])
    u, R, adj = build(p)
    N = len(R)
    deg = adj.sum(1)
    print('p', p, 'u', u, 'N', N, 'degree min/max/mean', deg.min(), deg.max(), round(deg.mean(), 2),
          'density', round(deg.mean() / (N - 1), 4))
    np.save(f'adj_q{p}.npy', adj)
    np.save(f'reps_q{p}.npy', R)
    with open(f'adj_q{p}.bin', 'wb') as f:
        f.write(np.int32(N).tobytes())
        f.write(adj.astype(np.uint8).tobytes())
