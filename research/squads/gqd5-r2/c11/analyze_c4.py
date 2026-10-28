import sys, json
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import numpy as np
from gqlib import Q4
G = Q4(5)
d = json.load(open('/home/user/degree-diameter/research/squads/gqd5-r1/c4/best.json'))
R, M = d['R'], d['M']
print('R', R, 'pairwise col', [[int(G.col[a,b]) for b in R] for a in R])
MR = [M[x] for x in R]
print('M(R)', MR, 'pairwise con', [[int(G.con[a,b]) for b in MR] for a in MR])
# triad centres of R in Q4 (points collinear with all of R, not in R)
def centres_pts(S):
    c = np.ones(G.np, dtype=bool)
    for s in S: c &= G.col[s] 
    return list(np.nonzero(c)[0])
def centres_lines(S):
    c = np.ones(G.nl, dtype=bool)
    for s in S: c &= G.con[s]
    return list(np.nonzero(c)[0])
print('triad centres of R (points):', centres_pts(R))
print('triad centres of M(R) (lines):', centres_lines(MR))
# which of M(col(x)) etc. : check local duality pattern
for x in R:
    a = np.nonzero(G.col[x])[0]
    img = set(M[p] for p in a)
    con = set(np.nonzero(G.con[M[x]])[0])
    print('x',x,'|M(col x) cap con M(x)|=',len(img & con), 'of', len(con), ' R-cols:', [r for r in R if G.col[x,r]])
    # points p in col(x) with M(p) not in con(M(x))
    bad = [p for p in a if M[p] not in con]
    print('   col(x) points whose image not concurrent with M(x):', len(bad), 'in R?', [p for p in bad if p in R])
