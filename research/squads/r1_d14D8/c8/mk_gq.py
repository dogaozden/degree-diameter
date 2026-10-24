"""mk_gq.py: cyclic voltage lift of the symplectic GQ W(q) incidence graph (degree q+1), plus k extra
random point-line matchings (k=0 for q=13 gives degree 14 directly; q=11 with k=2 gives degree 14).
Voltages: zero (mode 0), or uniform random in Z_m (mode r, seed).
python3 mk_gq.py q m mode seed k out      (mode: z | r)
Writes base file: 'N N m' then 'p l v' lines (points = side A, lines = side B)."""
import sys
import numpy as np
from gq import build

def make(q, m, mode, seed, k, out):
    N, LP, PL = build(q)
    rng = np.random.default_rng(seed)
    ps = LP.reshape(-1)
    ls = np.repeat(np.arange(N), q + 1)
    # incidence edges: (point, line)
    pts_of_line = LP  # (N, q+1)
    E_p = PL.reshape(-1)              # for each point its lines
    E_l = np.repeat(np.arange(N), q + 1)
    # use incidence as (point=ps, line=ls) with ps = LP[l][k]
    edges = [np.stack([ps, ls], axis=1)]
    inc = set(map(tuple, edges[0].tolist()))
    for j in range(k):
        perm = rng.permutation(N)
        # repair by swaps (keeps perm a permutation): each point p must avoid incidences and earlier matchings
        while True:
            bad = [p for p in range(N) if (p, int(perm[p])) in inc]
            if not bad:
                break
            for p in bad:
                if (p, int(perm[p])) not in inc:
                    continue
                for _ in range(100000):
                    r = int(rng.integers(N))
                    a, b = int(perm[p]), int(perm[r])
                    if (p, b) not in inc and (r, a) not in inc and r != p:
                        perm[p], perm[r] = b, a
                        break
                else:
                    raise RuntimeError('matching repair failed')
        ext = np.stack([np.arange(N), perm], axis=1)
        for a, b in ext.tolist():
            inc.add((a, b))
        edges.append(ext)
    allE = np.concatenate(edges, axis=0)
    if mode == 'z':
        V = np.zeros(len(allE), dtype=np.int64)
    else:
        V = rng.integers(0, m, len(allE))
    allE = np.concatenate([allE, V[:, None]], axis=1)
    with open(out, 'w') as f:
        f.write(f'{N} {N} {m}\n')
        np.savetxt(f, allE, fmt='%d')
    return N, len(allE)

if __name__ == '__main__':
    q, m, mode, seed, k, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
    N, E = make(q, m, mode, seed, k, out)
    print('wrote', out, 'N', N, 'edges', E, 'lift vertices', 2 * N * m)
