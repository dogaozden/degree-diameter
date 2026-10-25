# quick statistics of a point set on H(11): tightness of non-chosen points (number of chosen collinear points)
import sys, numpy as np
hexfn = '/home/user/degree-diameter/research/squads/c157b-r1/shared/hex_q11.bin'
b = open(hexfn, 'rb').read()
q, N, Lc = (int(x) for x in np.frombuffer(b[:12], dtype=np.int32)); Q1 = q + 1
LP = np.frombuffer(b[12:12 + 4 * Lc * Q1], dtype=np.int32).reshape(Lc, Q1).astype(np.int64)
ids = np.loadtxt(sys.argv[1], dtype=np.int64).reshape(-1)
s = np.zeros(N, bool); s[ids] = True
cnt = np.zeros(Lc, np.int64); cnt[:] = s[LP].sum(1)            # chosen points per line (<=1)
# tight[p] = number of chosen points collinear with p = number of lines through p that contain a chosen point (other than p)
cov = (cnt > 0).astype(np.int64)
tight = np.zeros(N, np.int64)
flat_p = LP.reshape(-1); flat_l = np.repeat(np.arange(Lc), Q1)
PL = flat_l[np.lexsort((flat_l, flat_p))].reshape(N, Q1)
tight = cov[PL].sum(1)                                           # lines through p containing a chosen point
tight_adj = tight - s.astype(np.int64) * 0                       # chosen points have tight = 0 on their own lines
ch = s
print('size', ids.size, 'lines covered', int(cov.sum()), 'of', Lc)
for name, m in [('chosen', ch), ('non-chosen', ~ch)]:
    v = np.bincount(tight[m], minlength=Q1 + 1)
    print(name, 'tight histogram (0..12):', v.tolist())
