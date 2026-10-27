import sys, pickle, time
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools')
import numpy as np
from q6lib import Geo, orbits
G = Geo(9)
N = G.N
Q1 = 10
# collinear neighbours: coll[p] = 90 points on lines through p other than p
_coll = None
def coll():
    global _coll
    if _coll is None:
        C = np.zeros((N, 90), dtype=np.int64)
        for p in range(N):
            lines = G.PL[p]
            pts = G.LP[lines].reshape(-1)
            pts = pts[pts != p]
            C[p] = np.sort(pts)
        _coll = C
    return _coll
D = pickle.load(open('/home/user/degree-diameter/research/squads/hexfam_r2/c1/roots9.pkl', 'rb'))
MATS, PERMS = D['mats'], D['perms']

def orbit_labels(perm_list):
    return orbits(N, perm_list)

def orbit_report(lab):
    """returns K, sizes, bad (orbit internally collinear), conflict matrix K x K (True if some point of i collinear with point of j, i!=j or same orbit internal)"""
    K = lab.max() + 1
    sizes = np.bincount(lab, minlength=K)
    C = coll()
    LC = lab[C]                      # labels of collinear neighbours
    LP_ = np.repeat(lab, 90).reshape(N, 90)
    conf = np.zeros((K, K), dtype=bool)
    conf[lab[:, None].repeat(90, 1).ravel(), LC.ravel()] = True
    bad = np.diag(conf).copy()
    return K, sizes, bad, conf

def is_ncol(ids):
    ids = np.asarray(ids)
    inset = np.zeros(N, dtype=bool); inset[ids] = True
    return not inset[coll()[ids]].any()
