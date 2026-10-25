"""q = 16 baselines for pairwise opposite sets of H(16) (partial ovoids of Q(6,16)).
(1) an elliptic quadric Q^-(3,16) inside a 4-space: q^2 + 1 = 257 points; (2) random greedy (best of a few runs)."""
import sys, numpy as np, itertools
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools'); from q6lib import Geo
G = Geo(16); q = 16; A, M = G.ADD, G.MUL
def tr(x):   # absolute trace GF(16) -> GF(2)
    s = 0; y = x
    for _ in range(4): s = A[s, y]; y = M[y, y]
    return s
beta = next(b for b in range(1, q) if tr(M[b, b]) == 1)
# W = {(x0, a, 0, c, x4, b, 0) : c = a + beta b}; Q|W = x0x4 + a^2 + ab + beta^2 b^2 (elliptic)
vecs = []
for x0, x4, a, b in itertools.product(range(q), repeat=4):
    if not (x0 or x4 or a or b): continue
    c = A[a, M[beta, b]]
    v = [x0, a, 0, c, x4, b, 0]
    Qv = A[A[A[M[x0, x4], M[a, b]], M[c, c]], 0]
    if Qv == 0: vecs.append(v)
ids = np.unique(G.ids_of(np.array(vecs)))
open('ell257.txt', 'w').write('\n'.join(map(str, ids.tolist())) + '\n')
print('elliptic section points', len(ids))
rng = np.random.default_rng(1); best = []
for run in range(4):
    mask = np.ones(G.N, bool); S = []
    while mask.any():
        idx = np.nonzero(mask)[0]; x = int(idx[rng.integers(len(idx))]); S.append(x)
        mask &= (G.B(G.C, G.C[[x]])[:, 0] != 0); mask[x] = False
    print('greedy run', run, len(S), flush=True)
    if len(S) > len(best): best = S
open('greedy.txt', 'w').write('\n'.join(map(str, best)) + '\n')
