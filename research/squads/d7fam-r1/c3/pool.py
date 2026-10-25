import numpy as np, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d7fam-r1/c3')
from hexmod import Hex
SQ = '/tmp/claude-0/-home-user-degree-diameter/0ecf9576-c77c-5462-b736-5bb1ddd9e678/scratchpad/w/sq'
H = Hex(SQ + '/hex_q5.bin'); N = H.N
R = np.load(SQ + '/R_q5.npy').astype(np.int64); S = [int(v) for v in np.load(SQ + '/S_q5.npy')]
st = np.load(SQ + '/state_q5_F9.npz'); Rs = st['R'].astype(np.int64); X = st['X'].astype(np.int64); L = st['L'].astype(np.int64)
print('R_q5', len(R), 'state R', len(Rs), 'k', len(X), 'L', len(L), 'same R?', sorted(R.tolist()) == sorted(Rs.tolist()))
# pairwise opposite / collinear checks
Bm = H.Bmat(R, R); np.fill_diagonal(Bm, 1); print('R pairwise opposite', (Bm != 0).all())
coll_R = set()
for r in R: coll_R |= H.collinear_points(int(r))
print('collinear-with-R union size', len(coll_R), 'closed nbhd sum', 31 * len(R))
# pool arithmetic
exc = set()
for l in L:
    exc |= H.lines_meeting(int(l)) & set(S)
print('excluded spread lines', len(exc), 'usable pool', len(S) - len(exc))
# points opposite to all of R (extension candidates for a bigger base set)
opp_all = np.ones(N, dtype=bool)
for r in R:
    B = H.Bmat(np.array([int(r)]), np.arange(N))[0]
    opp_all &= (B != 0)
opp_all[R] = False
print('points opposite to all of R (R-extension candidates):', int(opp_all.sum()))
# candidate extras: points non-collinear with R
cand = np.ones(N, dtype=bool); cand[list(coll_R)] = False; cand[R] = False
print('candidate extra points (non-collinear with R, not in R):', int(cand.sum()))
