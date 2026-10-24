import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d13D7_r3/c7')
from cov_check import read_offsets, cov
from common import *
NS = {2,6,7,8,10}
sq = {(x*x) % 11 for x in range(1, 11)}
# all 14641 vertices as (s,b,c,f)
V4 = np.array([(s, b, c, f) for s in range(11) for b in range(11) for c in range(11) for f in range(11)])
def D(w):
    return (w[..., 0]**2 + 3*w[..., 2]**2 + 8*w[..., 1]*w[..., 3]) % 11
Dv = D(V4)
isNS = np.isin(Dv, list(NS))
def adj_row(v):
    # adjacency of all vertices to v (difference w - v)
    diff = (V4 - v) % 11
    return isNS[ (np.array(D(diff)) ) ] if False else np.isin(D(diff), list(NS))
def clique_stats(Vs):
    Vs = [tuple(v) for v in Vs]
    m = np.zeros(len(V4), dtype=int)
    for v in Vs:
        m += ~adj_row(np.array(v))
    inK = np.zeros(len(V4), bool)
    for v in Vs:
        idx = int(np.where((V4 == v).all(1))[0][0]); inK[idx] = True
    m_out = m[~inK]
    return {'addable(m=0)': int((m_out == 0).sum()), 'm=1': int((m_out == 1).sum()), 'm=2': int((m_out == 2).sum()), 'm=3': int((m_out==3).sum())}
if __name__ == '__main__':
    V = read_offsets(sys.argv[1])
    print('cov', cov(V), clique_stats(V))
