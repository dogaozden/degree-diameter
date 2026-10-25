import numpy as np, sys, collections, random
sys.path.insert(0, '.')
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
H = Hex(SP + 'hex_q13.bin'); q = H.q
R = np.loadtxt(SP + 'R792_q13_idx.txt', dtype=np.int64, comments='#')
S = np.loadtxt(SP + 'S_q13_spread.txt', dtype=np.int64, comments='#')
print('q', q, 'N', H.N, '|R|', len(R), '|S|', len(S))
Bm = H.Bmat(R, R); np.fill_diagonal(Bm, 1); print('R pairwise opposite:', bool((Bm != 0).all()))
np.save(SP + 'R792idx.npy', R); np.save(SP + 'S13.npy', S)
colR = np.zeros(H.N, bool); colR[H.lp[H.pl[R]].reshape(-1)] = True; colR[R] = True
cand = np.nonzero(~colR)[0]
c = np.zeros(len(cand), dtype=np.int64)
for s in range(0, len(cand), 20000):
    c[s:s+20000] = (H.Bmat(cand[s:s+20000], R) == 0).sum(1)
print('candidates', len(cand), 'c distribution', sorted(collections.Counter(c.tolist()).items())[:12])
Sset = set(S.tolist()); rng = random.Random(1); prof = collections.Counter()
for l in rng.sample(range(H.N), 200):
    if l in Sset: continue
    d2, d4 = H.line_ball(l); prof[(len(Sset & d2), len(Sset & d4))] += 1
print('S profile (concurrent, distance 4) of random lines:', prof.most_common(5))
