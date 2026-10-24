"""mk_init.py q m seed out [nmatch=2] [hexmode=rand|zero]
H(q) incidence edges (hexagon voltages uniform in Z_m, or 0) + nmatch extra perfect matchings points -> lines
(avoiding hexagon pairs and repeated pairs), extra voltages uniform in Z_m.
Edge order: the N*(q+1) hexagon edges (hex_edges order: line by line), then matching j as block of N edges
(point p at index NH + j*N + p), as expected by sa.c."""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work')
from hexlib import load, write_base, hex_edges
q, m, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
nm = int(sys.argv[5]) if len(sys.argv) > 5 else 2
hexmode = sys.argv[6] if len(sys.argv) > 6 else 'rand'
N, LP, PL, coord = load(q)
rng = np.random.default_rng(seed)
volt = rng.integers(0, m, size=LP.shape) if hexmode == 'rand' else np.zeros(LP.shape, dtype=np.int64)
E = [hex_edges(LP, volt)]
used = set((int(p), int(l)) for l in range(N) for p in LP[l])
for j in range(nm):
    M = rng.permutation(N)
    bad = True
    while bad:
        bad = False
        for p in range(N):
            if (p, int(M[p])) in used:
                bad = True
                p2 = int(rng.integers(N))
                M[p], M[p2] = M[p2], M[p]
        if bad:
            # re-check after swaps; loop until clean
            pass
    for p in range(N):
        used.add((p, int(M[p])))
    E.append(np.stack([np.arange(N), M, rng.integers(0, m, N)], axis=1))
write_base(out, N, m, np.concatenate(E))
print('wrote', out, 'N', N, 'edges', sum(len(e) for e in E), file=sys.stderr)
