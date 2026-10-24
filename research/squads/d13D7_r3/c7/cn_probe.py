import sys, random, time, numpy as np
sys.argv_saved = sys.argv; sys.argv = ['x']
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d13D7_r3/c7')
from common import *
from cov_check import read_offsets, cov
NSET = [2, 6, 7, 8, 10]
V4 = np.array([(s, b, c, f) for s in range(11) for b in range(11) for c in range(11) for f in range(11)])
def Dq(w): return (w[..., 0]**2 + 3*w[..., 2]**2 + 8*w[..., 1]*w[..., 3]) % 11
isNS = np.zeros(11, bool); isNS[NSET] = True
def vid(v): s, b, c, f = v; return s*1331 + b*121 + c*11 + f
def adjrow(i):
    # boolean over all vertices: adjacent to vertex i (vertex index)
    v = V4[i]
    return isNS[Dq((V4 - v) % 11)]
def read_idx(path):
    out = []
    for line in open(path):
        t = line.split()
        if not t or t[0].startswith('#'): continue
        a, b, c, e, f = [int(z) for z in t[:5]]
        out.append(vid(((e + 2*a) % 11, b % 11, c % 11, f % 11)))
    return out
if __name__ == '__main__':
    K0 = read_idx('/home/user/degree-diameter/research/d13D7/sets/R320_offsets29_u1-0-0-9-0.txt')
    print('K0', len(K0), 'cov', cov([V4[i] for i in K0]))
    rng = random.Random(1)
    rows = {i: adjrow(i) for i in K0}
    for r in [2, 3, 4, 5, 6, 8, 10, 12]:
        R = rng.sample(K0, r)
        Kp = [i for i in K0 if i not in R]
        mask = np.ones(len(V4), bool)
        for y in Kp: mask &= rows[y]
        mask[Kp] = False
        cn = np.nonzero(mask)[0]
        # induced adjacency among CN
        sub = np.array([[isNS[Dq((V4[a]-V4[b]) % 11)] if a != b else False for b in cn] for a in cn]) if len(cn) < 400 else None
        dens = sub.mean() if sub is not None else -1
        print('r', r, '|CN|', len(cn), 'R in CN', all(x in set(cn.tolist()) for x in R), 'density', round(float(dens), 3) if dens >= 0 else 'n/a')
