import numpy as np, sys
from analyze1 import load
grp = sys.argv[1]
T = {'psl': 588984, 'prod': 592704}
_, R, O = load('stats_rand_%s.tsv' % grp)
_, G, OG = load('stats_good_%s.tsv' % grp)
_, C, OC = load('stats_ce_%s.tsv' % grp)
def coll(A):
    # collisions at distance 3 (B side, full tree = 1+10*9*9 = 820), distance 4 (A side) and 5 (B side)
    return 820 - A[:, 5], A[:, 6]   # lev[2] is index 5 in rows (cols: E,P,F,lev0..lev6) -> rows[:,3+2]
c3R = 820 - R[:, 5]; c3G = 820 - G[:, 5]; c3C = 820 - C[:, 5]
print('collisions at distance 3 (820 - ball): random dist', np.unique(c3R, return_counts=True))
print('good:', np.unique(c3G, return_counts=True), ' chain-ends:', np.unique(c3C, return_counts=True))
for c in np.unique(c3R)[:8]:
    m = c3R == c
    e = R[m, 0]
    print('random with c3=%d: n=%5d  energy median %6.1f  p1 %5.1f  frac energy<=60 %.3f' % (c, m.sum(), np.median(e), np.percentile(e, 1), (e <= 60).mean()))
# distance-4 and -5 deficiency vs energy among random sets
for name, col, full in [('dist4 (A side, tree 1+90+...)', 6, None)]:
    pass
# partial relation: energy vs c3 among random sets with the same plain cost bin
bins = [0, 60, 90, 120, 160, 250, 1e9]
print('energy bins vs mean c3 among random sets:')
for lo, hi in zip(bins[:-1], bins[1:]):
    m = (R[:, 0] >= lo) & (R[:, 0] < hi)
    if m.sum() == 0: continue
    print('  energy [%g,%g): n=%5d  mean c3 %.2f  frac c3=0 %.3f' % (lo, hi, m.sum(), c3R[m].mean(), (c3R[m] == 0).mean()))
print('chain-ends by energy: mean c3, frac c3=0')
for e in np.unique(C[:, 0]):
    m = C[:, 0] == e
    print('  energy %g n=%d mean c3 %.2f frac0 %.3f' % (e, m.sum(), c3C[m].mean(), (c3C[m] == 0).mean()))
