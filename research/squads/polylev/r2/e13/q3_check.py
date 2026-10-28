"""q=3 check of the sample sets: are they 4-dominating (line side)? pairwise point-disjoint?"""
import numpy as np
from common import *
H = load(3)
nonpen = np.load('q3_nonpencil_containing0.npy')
Lpts = [set(H.lines[l].tolist()) for l in range(H.L)]
def opp_dist_ok(S):
    # brute-force check using point-line incidence BFS (independent of ball_matrix)
    adj = {}
    for l in range(H.L):
        for p in H.lines[l]:
            adj.setdefault(('L', l), []).append(('P', int(p)))
            adj.setdefault(('P', int(p)), []).append(('L', l))
    def dist(src):
        d = {src: 0}; fr = [src]
        for k in range(1, 5):
            nf = []
            for v in fr:
                for w in adj[v]:
                    if w not in d:
                        d[w] = k; nf.append(w)
            fr = nf
        return d
    reach = set()
    for m in S:
        reach |= {v[1] for v in dist(('L', m)) if v[0] == 'L'}
    return len(reach) == H.L
ok = all(opp_dist_ok(list(map(int, s))) for s in nonpen[:5])
print('first 5 non-pencil sets dominate (brute BFS radius 4):', ok)
s = list(map(int, nonpen[0]))
print('pairwise line distances in first set:', [[int(np.load('ball4_q3.npy')[a, b]) for b in s] for a in s])
