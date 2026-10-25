import numpy as np, sys, os, collections
sys.path.insert(0, '.')
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
H = Hex(SP + 'hex_q11.bin'); st = np.load(sys.argv[1])
R, Xs, Ls = st['R'], st['X'], st['L']; S = np.load(SP + 'S_herm.npy'); k = len(Xs)
NR = (H.Bmat(Xs, R) == 0)                          # k x 756
Sline = -np.ones(H.N, dtype=np.int64)
for j, l in enumerate(S): Sline[H.lp[l]] = j
LS4 = np.zeros((k, len(S)), bool); LS2 = np.zeros((k, len(S)), bool)
for j, l in enumerate(Ls):
    conc = Sline[H.lp[l]]; conc = conc[conc >= 0]; LS2[j, conc] = True
    near = Sline[H.lp[H.pl[H.lp[l]]].ravel()]; near = near[near >= 0]; LS4[j, near] = True
LS4 &= ~LS2
ex = LS2.any(0)
tR = collections.Counter(tuple(np.nonzero(NR[:, i])[0]) for i in range(len(R)))
tS = collections.Counter(tuple(np.nonzero(LS4[:, i])[0]) for i in range(len(S)) if not ex[i])
by = collections.defaultdict(lambda: [0, 0, 0])
for t, n in tR.items(): by[len(t)][0] += n; by[len(t)][2] += 1
for t, n in tS.items(): by[len(t)][1] += n
print('k =', k, '| c(x) =', NR.sum(1).tolist())
print('per type size: |t|: (R points, S lines, distinct R types)', dict(sorted(by.items())))
tight = sorted(((tS.get(t, 0) - n, t, n) for t, n in tR.items()))[:8]
print('tightest types (slack, type, R count):', tight)
ov = NR.astype(int) @ NR.T.astype(int); np.fill_diagonal(ov, 0)
ovS = LS4.astype(int) @ LS4.T.astype(int); np.fill_diagonal(ovS, 0)
print('R pair overlaps: mean %.1f max %d | S pair overlaps: mean %.1f min %d' % (ov.sum() / (k * (k - 1)), ov.max(), ovS.sum() / (k * (k - 1)), ovS[~np.eye(k, dtype=bool)].min()))
