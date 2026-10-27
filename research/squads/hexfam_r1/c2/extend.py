"""usage: python3 extend.py q setfile outfile tlimit : add a max clique of the points opposite to every point of the set"""
import sys, time, numpy as np
sys.path.insert(0,'/home/user/degree-diameter/research/squads/hexfam_r1/c2')
sys.path.insert(0,'/home/user/degree-diameter/research/projects/hexagon-family/tools')
from q6lib import Geo
from common import write_set
from mwc import max_weight_clique
q = int(sys.argv[1]); sf = sys.argv[2]; outf = sys.argv[3]; tl = float(sys.argv[4])
G = Geo(q)
S = np.array([int(x) for x in open(sf).read().split()], dtype=np.int64)
Bm = G.B(G.C, G.C[S]) != 0          # N x |S|
ext = np.nonzero(Bm.all(axis=1) & ~np.isin(np.arange(G.N), S))[0]
print('set', len(S), 'ext candidates', len(ext), flush=True)
if len(ext):
    O = G.B(G.C[ext], G.C[ext]) != 0
    adj = []
    for a in range(len(ext)):
        bits = 0
        for b in np.nonzero(O[a])[0]:
            if b != a: bits |= 1 << int(b)
        adj.append(bits)
    w, verts, exact = max_weight_clique([1]*len(ext), adj, tlimit=tl)
    add = ext[verts]
    print('added', len(add), 'exact', exact, flush=True)
    S = np.concatenate([S, add])
ok, e = G.check_opp(S)
print('final size', len(S), 'check_opp', ok, 'remaining ext', e, flush=True)
write_set(outf, S)
print('wrote', outf)
