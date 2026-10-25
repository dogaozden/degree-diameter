import sys, time, collections, itertools, random, pickle
sys.path.insert(0, '/home/user/degree-diameter/research/squads/hexfam_r2/c1')
from fastlib import *
EXTRA = pickle.load(open('/home/user/degree-diameter/research/squads/hexfam_r2/c1/extra9.pkl', 'rb'))
RN = list(MATS.keys())
def evaluate(perm_list, tl=10, kmax=3000):
    lab = forb(perm_list)
    K = lab.max() + 1
    if K > kmax:
        return dict(K=int(K), skip=True)
    K, sizes, bad, conf = summarize(lab)
    good = [i for i in range(K) if not bad[i]]
    if not good:
        return dict(K=int(K), good=0, best=0)
    best, verts, exact = mwis_exact(sizes, good, conf, tl)
    return dict(K=int(K), good=len(good), gsizes=sorted(sizes[good].tolist())[-8:], best=int(best), exact=bool(exact), chosen=verts, lab=lab, sizes=sizes)
