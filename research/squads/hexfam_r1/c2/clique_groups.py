"""usage: python3 clique_groups.py q groups.npy tlimit outprefix
Compatibility of pairwise-opposite point groups (all cross pairs opposite), then max-weight clique."""
import sys, time, numpy as np
sys.path.insert(0,'/home/user/degree-diameter/research/squads/hexfam_r1/c2')
sys.path.insert(0,'/home/user/degree-diameter/research/projects/hexagon-family/tools')
from q6lib import Geo, A7
from common import write_set
from mwc import max_weight_clique
q = int(sys.argv[1]); gfile = sys.argv[2]; tl = float(sys.argv[3]); outp = sys.argv[4]
G = Geo(q)
groups = [np.asarray(g, dtype=np.int64) for g in np.load(gfile, allow_pickle=True)]
K = len(groups); t0 = time.time()
P = np.concatenate(groups); U, inv = np.unique(P, return_inverse=True)
starts = np.concatenate([[0], np.cumsum([len(g) for g in groups])])
CU = G.C[U].astype(np.float64)
A7f = A7.astype(np.float64)
inc = np.zeros((K, K), dtype=bool)
for a in range(K):
    Ca = G.C[groups[a]].astype(np.float64)
    Z = np.mod(Ca @ A7f @ CU.T, q) == 0          # s x |U| : non-opposite pairs (incl. identical points)
    bad = Z.any(axis=0)
    inc[a] = np.logical_or.reduceat(bad[inv], starts[:-1])
inc = inc | inc.T
np.fill_diagonal(inc, True)
print('K', K, 'U', len(U), 'compat built', round(time.time()-t0, 1), 'density of compat', round(1-inc.mean(), 4), flush=True)
w = [len(g) for g in groups]
adj = []
for a in range(K):
    bits = 0
    for b in np.nonzero(~inc[a])[0]: bits |= (1 << int(b))
    adj.append(bits)
bw, verts, exact = max_weight_clique(w, adj, tlimit=tl)
pts = np.concatenate([groups[v] for v in verts]) if verts else np.array([], dtype=np.int64)
ok, ext = G.check_opp(pts) if len(pts) else (True, 0)
print('MWC weight', bw, 'exact', exact, 'groups', len(verts), 'check_opp', ok, 'ext', ext, 'time', round(time.time()-t0,1), flush=True)
out = '%s_q%d_%d.txt' % (outp, q, len(pts))
write_set(out, pts)
print('wrote', out, flush=True)
