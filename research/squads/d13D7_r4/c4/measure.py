#!/usr/bin/env python3
"""Card c4 (squad round 4): blocking statistics of a point set S of H(11) (outside points y: cnt[y] = #{s in S: B(s,y)=0})."""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/d13D7/tools')
import hexlib

def main():
    idx_path = sys.argv[1]
    q, lines, P = hexlib.load('/home/user/degree-diameter/research/d13D7/hex/hex_q11.bin')
    P = P.astype(np.int64)
    N = P.shape[0]
    S = np.loadtxt(idx_path, comments='#', dtype=np.int64).reshape(-1)
    inS = np.zeros(N, bool); inS[S] = True
    J = np.zeros((7, 7), np.int64)
    J[0, 4] = J[4, 0] = J[1, 5] = J[5, 1] = J[2, 6] = J[6, 2] = 1
    J[3, 3] = -2
    PJ = (P @ J) % 11          # row y = (J y)^T ; B(x, y) = PJ[y] . x
    cnt = np.zeros(N, np.int64)
    X = P[S]
    for s in range(0, len(S), 90):
        G = (PJ @ X[s:s + 90].T) % 11      # N x chunk : B(y, s_j)
        cnt += (G == 0).sum(axis=1)
    cnt[S] -= 1                 # B(s,s) = 0 for points of the quadric; remove self count
    out = ~inS
    c = cnt[out]
    print('set size', len(S), 'outside points', out.sum())
    print('cnt over outside points: min', c.min(), 'max', c.max(), 'mean %.2f' % c.mean())
    vals, counts = np.unique(c, return_counts=True)
    print('lowest cnt values:', list(zip(vals[:12].tolist(), counts[:12].tolist())))
    print('outside points with cnt==1:', int((c == 1).sum()), ' cnt==2:', int((c == 2).sum()), ' cnt<=3:', int((c <= 3).sum()))
    # private candidates per set point (outside points with cnt == 1 blocked by that point)
    priv = np.zeros(len(S), np.int64)
    # set points: cnt of each set point among other set points
    cs = cnt[S]
    print('set points: min cnt-in-set', 0, ' (set is pairwise opposite, cnt(s) counts only outside blockers)')
    print('check: blockers of set points inside S:', int(cs.sum()))
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
