"""Loop model: a Z_M lift (M even) of H(q) with a loop at every vertex instead of hop matchings.

Lift vertex (u, a), a in Z_M.  H-edges (p, a) ~ (L, a + phi(p, L)) with phi even; the loop at u gives
(u, a) ~ (u, a +- c_u) with c_u odd and 2c_u != 0.  The lift is bipartite (colour = side of u + a mod 2)
and (q+3)-regular, with M|GH(q)| vertices.  (liftdiam reports the base as non-bipartite because of the loops.)

usage: python3 loopmodel.py q M mode seed out.txt
  mode zero: phi = 0, c_u uniform random odd;  holo: phi uniform random even, c_u random odd;
  const: phi = 0, c_u = 1 (the Cartesian product H(q) x C_M, diameter 6 + M/2)
"""
import random
import sys

import gh


def build(q, M, mode, seed):
    assert M % 2 == 0
    rng = random.Random(seed)
    H = gh.load(q)
    N = H.N
    odd = [c for c in range(1, M, 2) if (2 * c) % M != 0]
    edges = []
    for p, L in gh.flags(H):
        phi = 2 * rng.randrange(M // 2) if mode == 'holo' else 0
        edges.append((p, L, phi, 0))
    for u in range(2 * N):
        c = 1 if mode == 'const' else rng.choice(odd)
        edges.append((u, u, c, 0))
    return 2 * N, edges


if __name__ == '__main__':
    q, M, mode, seed, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), sys.argv[5]
    NB, edges = build(q, M, mode, seed)
    gh.write_base(out, NB, M, 1, edges)
