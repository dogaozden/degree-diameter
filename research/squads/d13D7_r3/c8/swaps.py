import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/d13D7/tools')
import hexlib
q, lines, coord = hexlib.load('/home/user/degree-diameter/research/d13D7/hex/hex_q11.bin')
N = len(coord)
R = [int(l) for l in open('/home/user/degree-diameter/research/squads/d13D7_r2/c6/best_idx.txt') if l.strip() and not l.startswith('#')]
P = coord[R]
C = coord.astype(np.int64)
# B(x, r) for all x against R: shape N x len(R)
W = np.stack([C[:, 4], C[:, 5], C[:, 6], (-2 * C[:, 3]) % q, C[:, 0], C[:, 1], C[:, 2]], axis=1)  # wd (x side)
Bm = (W @ P.T.astype(np.int64)) % q   # Bm[x, j] = B(x, R_j) for coefficient form: careful
# B(x,y) = sum_k wd(x)_k * co(y)_k with co(y)=P rows
cnt = (Bm == 0).sum(axis=1)
for j, r in enumerate(R):
    cnt[r] -= 1  # a point of R is counted against itself (B(r,r)=0)
inR = np.zeros(N, bool); inR[R] = True
print('cnt histogram over non-R points:', np.bincount(cnt[~inR])[:12])
# for cnt==1 points find their unique partner y in R
ones = np.where((cnt == 1) & (~inR))[0]
partner = {}
for x in ones:
    js = np.where(Bm[x] == 0)[0]
    js = [j for j in js if R[j] != x]
    partner.setdefault(R[js[0]], []).append(x)
print('cnt=1 points:', len(ones), ' distinct partners:', len(partner), ' group sizes:', sorted([len(v) for v in partner.values()])[-10:])
# (1,2)-swap check: two opposite points with the same single partner
best_pair = 0
for y, xs in partner.items():
    for a in range(len(xs)):
        for b in range(a + 1, len(xs)):
            xa, xb = xs[a], xs[b]
            if int(np.dot(W[xa], C[xb])) % q != 0:
                best_pair += 1
print('(1,2)-swaps available:', best_pair)
