# hexmod.py: copy of research/cell147/mirror/hexmod.py (branch claude/cell-14-7-record-5d03gb), used by addscan.py and probe3.py
"""H(q) from hexgen.c output (research/d13D7/hexgen.c): points of Q = x0x4+x1x5+x2x6-x3^2 (hexgen order),
lines as (q+1)-point lists.  Distances in the incidence graph: point-point 0/2/4/6, line-line 0/2/4/6,
point-line 1/3/5."""
import numpy as np
class Hex:
    def __init__(self, path):
        with open(path, 'rb') as f:
            q, N, L = np.frombuffer(f.read(12), dtype=np.int32)
            self.q, self.N = int(q), int(N)
            self.lp = np.frombuffer(f.read(4 * L * (q + 1)), dtype=np.int32).reshape(L, q + 1).copy()
            self.X = np.frombuffer(f.read(N * 7), dtype=np.uint8).reshape(N, 7).astype(np.int64)
        q = self.q
        self.pl = np.zeros((self.N, q + 1), dtype=np.int32); c = np.zeros(self.N, dtype=np.int64)
        for l in range(self.N):
            for p in self.lp[l]:
                self.pl[p, c[p]] = l; c[p] += 1
        assert (c == q + 1).all()
        self.code = {}
        w = q ** np.arange(7)
        codes = (self.X * w).sum(axis=1)
        self.code = dict(zip(codes.tolist(), range(self.N)))
    def index_of(self, coords):
        q = self.q; X = np.asarray(coords, dtype=np.int64) % q
        inv = np.array([0] + [pow(i, q - 2, q) for i in range(1, q)])
        first = np.argmax(X != 0, axis=1); X = X * inv[X[np.arange(len(X)), first]][:, None] % q
        codes = (X * (q ** np.arange(7))).sum(axis=1)
        return np.array([self.code[c] for c in codes.tolist()])
    def B(self, i, j):
        x, y = self.X[i], self.X[j]; q = self.q
        return int(x[0]*y[4]+x[4]*y[0]+x[1]*y[5]+x[5]*y[1]+x[2]*y[6]+x[6]*y[2]-2*x[3]*y[3]) % q
    def Bmat(self, I, J):
        q = self.q; X = self.X[I]; Y = self.X[J][:, [4, 5, 6, 3, 0, 1, 2]].copy(); Y[:, 3] = (-2 * Y[:, 3]) % q
        return (X @ Y.T) % q
    def line_ball(self, l, depth=4):
        """lines at distance 2 and 4 from line l (sets), via the incidence graph."""
        pts1 = set(self.lp[l].tolist())
        lines2 = set(self.pl[list(pts1)].ravel().tolist()) - {l}
        pts3 = set(self.lp[list(lines2)].ravel().tolist()) - pts1
        lines4 = set(self.pl[list(pts3)].ravel().tolist()) - lines2 - {l}
        return lines2, lines4
    def point_ball(self, p):
        """points at distance 2 and 4 from point p."""
        lines1 = set(self.pl[p].tolist())
        pts2 = set(self.lp[list(lines1)].ravel().tolist()) - {p}
        lines3 = set(self.pl[list(pts2)].ravel().tolist()) - lines1
        pts4 = set(self.lp[list(lines3)].ravel().tolist()) - pts2 - {p}
        return pts2, pts4
    def collinear_points(self, p):
        return set(self.lp[self.pl[p]].ravel().tolist()) - {p}
    def lines_meeting(self, l):
        return set(self.pl[self.lp[l]].ravel().tolist()) - {l}
