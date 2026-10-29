import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/c7')
from common import *
q = int(sys.argv[1])
q, N, LP, PL, X, G, spread_pts, spread_lines, v = setup(q)
inG = np.zeros(N, bool); inG[G] = True
cnt = inG[PL].sum(1)          # G-lines through each point
print('q', q, 'N', N, '|G|', len(G), 'valid', valid(LP, PL, N, G), 'v', v, 'nspread_lines', len(spread_lines), 'spread pts', len(spread_pts))
print('v in spread_lines', v in set(spread_lines.tolist()), 'v in G', inG[v])
uncov = np.nonzero(cnt == 0)[0]
print('uncovered points', len(uncov), 'uncovered in spread', len(np.intersect1d(uncov, spread_pts)), 'covered spread pts', len(spread_pts) - len(np.intersect1d(uncov, spread_pts)))
print('points covered >=2 times', int((cnt >= 2).sum()), 'by 1', int((cnt == 1).sum()), 'by 0', int((cnt == 0).sum()))
# spread lines other than v: number of points carrying a G-line
sl = [int(l) for l in spread_lines if l != v]
carry = np.array([int((cnt[LP[l]] > 0).sum()) for l in sl])
from collections import Counter
print('spread lines (other than v):', len(sl), 'carry histogram (# points with G-line):', sorted(Counter(carry.tolist()).items()))
# which spread lines in G?
print('spread lines in G:', sum(inG[l] for l in sl))
# for the spread line of v's line set: how many points of spread lines are on v-meeting lines
