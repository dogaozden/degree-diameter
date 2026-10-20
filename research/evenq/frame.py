"""The D = 6 frame for even q: v = <e1, e6>, Pi_z : X3 = X0 + d X4 + a X2 + b X5 (Tr(d) = 1), S_z, free points.

    from frame import Frame;  Fr = Frame(q)
"""
import os

import numpy as np

from hexq import load


class Frame:
    def __init__(self, q, delta=None, log=print):
        H = load(q, log)
        self.H = H
        F = H.F
        assert F.p == 2, 'even q only'
        self.q, self.N = q, H.N
        P, lines, N = H.P, H.lines, H.N
        if delta is None and os.environ.get('EVENQ_DELTA'):
            delta = int(os.environ['EVENQ_DELTA'])
        self.delta = delta if delta is not None else next(d for d in range(1, q) if H.tr(d) == 1)
        e = np.eye(7, dtype=np.int64)
        i1 = self.index_of(e[1:2])[0]
        i6 = self.index_of(e[6:7])[0]
        v = [k for k in H.through[i1] if i6 in lines[k]]
        assert len(v) == 1
        self.v = v = int(v[0])
        # BFS distance from v
        dist = np.full(2 * N, -1)
        dist[N + v] = 0
        fr, d = [N + v], 0
        while fr:
            d += 1
            nxt = []
            for x in fr:
                for y in (lines[x - N] if x >= N else H.through[x] + N):
                    if dist[y] < 0:
                        dist[y] = d
                        nxt.append(int(y))
            fr = nxt
        self.dist = dist
        self.L0 = self.lin(P, 0, 0)  # X3 + X0 + d X4 on every point
        self.inPi = self.L0 == 0
        S = np.nonzero(self.inPi[lines].all(axis=1))[0]
        self.S = S
        self.Sline_of = np.full(N, -1)
        for s in S:
            self.Sline_of[lines[s]] = s
        self.free = np.nonzero(~self.inPi & (dist[:N] == 5))[0]

    def index_of(self, V):
        H, F = self.H, self.H.F
        first = np.argmax(V != 0, axis=1)
        lead = V[np.arange(len(V)), first]
        Vn = F.MUL[V, F.INV[lead][:, None]]
        c = Vn @ (self.H.q ** np.arange(7, dtype=np.int64))
        i = np.searchsorted(H.codes, c)
        assert np.all(H.codes[np.minimum(i, H.N - 1)] == c)
        return i

    def lin(self, X, a, b):
        """X3 + X0 + d X4 + a X2 + b X5 (rows of X)"""
        M, A = self.H.F.MUL, self.H.F.ADD
        out = A[A[X[:, 3], X[:, 0]], M[self.delta, X[:, 4]]]
        return A[A[out, M[a, X[:, 2]]], M[b, X[:, 5]]]

    def Sz(self, a, b):
        inz = self.lin(self.H.P, a, b) == 0
        return np.nonzero(inz[self.H.lines].all(axis=1))[0]
