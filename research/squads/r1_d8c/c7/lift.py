"""c7: lift of I(H(q)) + two matchings by G = Z_10 x Z_k (order m = 10k), explicit edge list for gcheck.

Lemma (Z_10 part): hexagon voltages have Z_10-part 0; matching t has Z_10-part a_t (a_1 = 1, a_2 = 4).
K-part (Z_k) is free on hexagon flags and on the matchings.
Vertex id of (base v, group element gi) = gi * 2N + v, base v: points 0..N-1, lines N..2N-1; gi = identity -> 0.
So sources range:0:2N (the identity fibre) meet every vertex orbit: exact check with gcheck EDGES 8 range:0:2N.
"""
import sys, os, subprocess, numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
from hexlib import load

_cache = {}
def hexdata(q):
    if q not in _cache:
        N, LP, PL, coord = load(q)
        _cache[q] = (N, LP)
    return _cache[q]

def group(k):
    G = 10 * k
    el = [(a, b) for a in range(10) for b in range(k)]   # index a*k+b
    idx = lambda a, b: (a % 10) * k + (b % k)
    add = np.array([[idx(el[x][0] + el[y][0], el[x][1] + el[y][1]) for y in range(G)] for x in range(G)], dtype=np.int64)
    return G, add, idx

def make_base(q, seed, k=None):
    """Matchings: sigma_t random bijections points -> lines (fixed by seed)."""
    N, LP = hexdata(q)
    rng = np.random.default_rng(seed)
    sig = np.stack([rng.permutation(N), rng.permutation(N)])
    return N, LP, sig

def write_lift(q, k, hexb, mb, sig, path, Nlp=None):
    """hexb: (N*(q+1),) Z_k values per flag f = l*(q+1)+j (point LP[l,j]); mb: (2, N) Z_k values per point of matching t."""
    N, LP = hexdata(q)
    G, add, idx = group(k)
    Q1 = q + 1
    # base edges: (u, v, voltage index)
    pts = LP.reshape(-1)                                  # point of flag f
    lns = np.repeat(np.arange(N), Q1)                     # line of flag f
    U = [pts]; V = [N + lns]; Vg = [np.array([idx(0, int(b)) for b in hexb])]
    for t, a in ((0, 1), (1, 4)):
        p = np.arange(N)
        U.append(p); V.append(N + sig[t]); Vg.append(np.array([idx(a, int(b)) for b in mb[t]]))
    U = np.concatenate(U); V = np.concatenate(V); Vg = np.concatenate(Vg)
    GI = np.arange(G)[:, None]
    tgt = add[GI, Vg[None, :]]                            # (G, E)
    src_id = (GI * (2 * N) + U[None, :]).reshape(-1)
    dst_id = (tgt * (2 * N) + V[None, :]).reshape(-1)
    with open(path, 'w') as f:
        f.write(f'{2 * N * G}\n')
        np.savetxt(f, np.stack([src_id, dst_id], axis=1), fmt='%d')
    return 2 * N * G

def gcost(path, D=8, spec=None):
    N, _ = hexdata(_q_of[0]) if False else (None, None)
    return None

def run_gcheck(path, nsrc, D=8):
    out = subprocess.run(['nice', '-n', '10', '/home/user/degree-diameter/research/squads/cells/d10D8_work/gcheck', path, str(D), f'range:0:{nsrc}'],
                         capture_output=True, text=True, env=dict(os.environ, OMP_NUM_THREADS='1'))
    line = [l for l in out.stdout.splitlines() if l.startswith('GCOST')]
    if not line:
        return None, out.stderr
    return int(line[0].split()[1]), line[0]
