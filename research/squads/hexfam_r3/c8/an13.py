import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools'); from q6lib import Geo
G = Geo(13); N, L = G.N, G.L
pairs = [tuple(map(int, l.split())) for l in open('/home/user/degree-diameter/research/squads/hexfam_r3/best_q13_815.pairs') if l.strip()]
R = np.array(sorted(set(open('/home/user/degree-diameter/research/d10D7/sets/P13_E7sub_E6_792.txt').read().split()), key=int), dtype=np.int64)
R = np.array([int(v) for v in open('/home/user/degree-diameter/research/d10D7/sets/P13_E7sub_E6_792.txt').read().split()])
Rb = np.array([p[0] for p in pairs[:len(R)]]); print('best first 792 == R set:', set(Rb.tolist()) == set(R.tolist()), len(pairs))
X = np.array([p[0] for p in pairs[len(R):]]); Sx = np.array([p[1] for p in pairs[len(R):]])
Sp = np.array([int(v) for v in open('/home/user/degree-diameter/research/d10D7/sets/L13_spread.txt').read().split()])
print('|Sp|', len(Sp), 'in pairs first', np.isin(np.array([p[1] for p in pairs[:len(R)]]), Sp).all())
nR = np.zeros(N, dtype=np.int64)
for a in range(0, N, 20000): nR[a:a+20000] = (G.B(G.C[a:a+20000], G.C[R]) == 0).sum(1)
print('|N(x) cap R| over all points: min', nR.min(), 'max', nR.max(), 'mean', nR.mean())
print('current x: sizes', nR[X].tolist())
M = (G.B(G.C[X], G.C[R]) == 0).astype(int)
print('overlap matrix of current x neighborhoods (max pairwise):', (M @ M.T - np.diag(np.diag(M @ M.T))).max(), 'sum of sizes', M.sum(), 'R-points hit', (M.sum(0)>0).sum())
print('hit multiplicity histogram over R', np.bincount(M.sum(0)))
