"""c12: Z_10 lift of a base multigraph with hub representatives.
Vertex (r, g) has id r + g*S, S = number of orbit representatives. Base edge (r1, r2, s) means (r1,g)~(r2,g+s) for all g.
Sources for an exact check: range:0:S (copy g=0 of every representative), valid because the whole graph is Z_10-invariant."""
import os, sys, subprocess, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
import hexlib

GCHECK = '/home/user/degree-diameter/research/squads/cells/d10D8_work/gcheck'
HERE = os.path.dirname(os.path.abspath(__file__))
M = 10

def lift_edges(S, base):
    base = np.asarray(base, dtype=np.int64).reshape(-1, 3)
    g = np.arange(M)
    out = []
    for r1, r2, s in base:
        u = r1 + g * S
        v = r2 + ((g + s) % M) * S
        out.append(np.stack([u, v], axis=1))
    return np.concatenate(out, axis=0)

def gcost(S, base, D, tag):
    E = lift_edges(S, base)
    fn = os.path.join(HERE, f'edges_{tag}.txt')
    with open(fn, 'w') as f:
        f.write(f'{M*S}\n')
        np.savetxt(f, E, fmt='%d')
    out = subprocess.run([GCHECK, fn, str(D), f'range:0:{S}'], capture_output=True, text=True,
                         env=dict(os.environ, OMP_NUM_THREADS='1'))
    line = [l for l in out.stdout.splitlines() if l.startswith('GCOST')]
    os.remove(fn)
    bad = int(line[0].split()[1]) if line else -1
    return bad, (line[0] if line else out.stderr[-300:])

def make_base(q, seed):
    N, LP, PL, coord = hexlib.load(q)
    rng = np.random.default_rng(seed)
    sig1 = rng.permutation(N); sig2 = rng.permutation(N)
    base = []
    for l in range(N):
        for p in LP[l]:
            base.append((int(p), N + l, 0))
    n_hex = len(base)
    match = [(p, N + int(sig1[p]), 1) for p in range(N)] + [(p, N + int(sig2[p]), 4) for p in range(N)]
    return N, base, match, sig1, sig2
