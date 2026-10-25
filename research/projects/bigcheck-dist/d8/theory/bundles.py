"""For SL(3,q)-invariant flag voltages: geodesic voltage vectors (signed counts per flag orbit) for bundles
between opposite points / opposite lines, from orbit representatives. Saves the distinct bundle types."""
import os, sys, numpy as np, itertools, collections
from geo import Geo, sl3, orbits
q = int(sys.argv[1])
SP = os.environ.get('SCRATCH', '/tmp')
H = Geo(f'/tmp/bcdt/hex/hex_q{q}.bin'); N = H.N
d = np.load(f'{SP}/sl3_q{q}.npz'); po, lo, gp, gl = d['po'], d['lo'], d['gp'], d['gl']
# flag orbit id
fl = {}
idx = 0
flag_list = [(p, l) for p in range(N) for l in H.plines[p]]
fid = {f: i for i, f in enumerate(flag_list)}
fperms = [np.array([fid[(gp[k][p], gl[k][l])] for (p, l) in flag_list]) for k in range(len(gp))]
fo = orbits(fperms, len(flag_list))
NF = fo.max() + 1
def forb(p, l): return fo[fid[(p, l)]]
# adjacency: vertex ids points 0..N-1, lines N..2N-1
def nbrs(v):
    return (H.plines[v] + N) if v < N else H.lines[v - N]
def geodesics_from(src):
    """all geodesics of length 6 from src to opposite vertices: dict target -> list of signed vectors"""
    res = collections.defaultdict(list)
    # DFS non-backtracking to depth 6, then keep targets at distance exactly 6 (all depth-6 non-backtracking
    # walks in a girth-12 graph are geodesics iff the endpoint is at distance 6)
    dist = {src: 0}
    frontier = [src]
    for dd in range(1, 7):
        nf = []
        for v in frontier:
            for w in nbrs(v):
                if w not in dist:
                    dist[w] = dd; nf.append(w)
        frontier = nf
    def rec(v, prev, depth, vec):
        if depth == 6:
            if dist.get(v) == 6: res[v].append(tuple(vec))
            return
        for w in nbrs(v):
            if w == prev: continue
            if dist.get(w) != depth + 1: continue
            vv = list(vec)
            if v < N: vv[forb(v, w - N)] += 1      # point -> line: +
            else: vv[forb(w, v - N)] -= 1          # line -> point: -
            rec(w, v, depth + 1, vv)
    rec(src, -1, 0, [0] * NF)
    return res
types = collections.Counter()
for kind, orb in (('P', po), ('L', lo)):
    for o in range(orb.max() + 1):
        rep = int(np.where(orb == o)[0][0])
        src = rep if kind == 'P' else rep + N
        g = geodesics_from(src)
        for t, vecs in g.items():
            assert len(vecs) == q + 1, len(vecs)
            # normalise: subtract first vector (bundle values up to translation)
            base = np.array(vecs[0])
            key = tuple(sorted(tuple(np.array(v) - base) for v in vecs))
            types[(kind, key)] += 1
print('q', q, 'flag orbits', NF, 'distinct bundle types (up to translation)', len(types))
import pickle
pickle.dump(dict(types), open(f'{SP}/bundles_q{q}.pkl', 'wb'))
