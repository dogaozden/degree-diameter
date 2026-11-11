"""H(q) built from the paper's Section 2.2 as printed: Q = X0X4+X1X5+X2X6 -/+ X3^2 and Tits' equations (2.1).
Points: normalised vectors (first non-zero coordinate 1). Lines: for each point x, the solution space of
b(x,y)=0 and the six Tits equations (linear in y) is computed; it must be a 3-space pi_x, whose lines through x are
the H(q)-lines on x."""
import itertools
from gf import GF
TITS = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)), ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]
class Hex:
    def __init__(self, q):
        F = self.F = GF(q); self.q = q; M, A, S = F.mul, F.add, F.sub
        self.even = (q % 2 == 0)
        E = list(F.elts())
        def Q(x):
            t = A[A[M[x[0]][x[4]]][M[x[1]][x[5]]]][M[x[2]][x[6]]]
            sq = M[x[3]][x[3]]
            return A[t][sq] if self.even else S[t][sq]
        self.Q = Q
        def bil(x, y):  # b(x,y) = Q(x+y)-Q(x)-Q(y)
            t = 0
            for (i, j) in ((0, 4), (1, 5), (2, 6)):
                t = A[t][A[M[x[i]][y[j]]][M[x[j]][y[i]]]]
            t3 = M[F.from_int(2)][M[x[3]][y[3]]]
            return A[t][t3] if self.even else S[t][t3]
        self.b = bil
        pts = []
        for lead in range(7):
            for rest in itertools.product(E, repeat=6 - lead):
                v = (0,) * lead + (1,) + rest
                if Q(v) == 0: pts.append(v)
        self.pts = pts; self.pid = {p: i for i, p in enumerate(pts)}
        N = (q + 1) * (q**4 + q*q + 1); assert len(pts) == N, (len(pts), N)
        self.N = N
        lines = {}; self.lines_on = [[] for _ in pts]
        for i, x in enumerate(pts):
            rows = []
            # b(x,y) = 0 as a linear form in y
            row = [0] * 7
            for (a, c) in ((0, 4), (1, 5), (2, 6)):
                row[c] = A[row[c]][x[a]]; row[a] = A[row[a]][x[c]]
            two = F.from_int(2)
            row[3] = (S[0][M[two][x[3]]] if not self.even else 0) if True else 0
            if self.even: row[3] = 0
            rows.append(row)
            for (i1, j1), (i2, j2) in TITS:
                # p_{i1 j1} - p_{i2 j2} = x_i1 y_j1 - x_j1 y_i1 - x_i2 y_j2 + x_j2 y_i2
                r = [0] * 7
                r[j1] = A[r[j1]][x[i1]]; r[i1] = S[r[i1]][x[j1]]
                r[j2] = S[r[j2]][x[i2]]; r[i2] = A[r[i2]][x[j2]]
                rows.append(r)
            basis = self.nullspace(rows)
            assert len(basis) == 3, (x, len(basis))
            # lines through x in span(basis): pick y in the space not prop. to x
            space = set()
            for coeffs in itertools.product(E, repeat=3):
                v = [0] * 7
                for c, bv in zip(coeffs, basis):
                    for k in range(7): v[k] = A[v[k]][M[c][bv[k]]]
                if any(v): space.add(self.norm(v))
            assert x in space and len(space) == q*q + q + 1
            seen = set()
            for y in space:
                if y == x or y in seen: continue
                L = frozenset(self.span_pts(x, y))
                seen |= L
                if L not in lines:
                    lines[L] = len(lines)
        self.lines = [None] * len(lines)
        for L, k in lines.items(): self.lines[k] = sorted(self.pid[p] for p in L)
        assert len(self.lines) == N
        for k, L in enumerate(self.lines):
            for i in L: self.lines_on[i].append(k)
        assert all(len(l) == q + 1 for l in self.lines_on)
        self.lid = {frozenset(L): k for k, L in enumerate(self.lines)}
    def norm(self, v):
        F = self.F
        for c in v:
            if c:
                ic = F.inv[c]; return tuple(F.mul[ic][t] for t in v)
    def span_pts(self, x, y):
        F = self.F; M, A = F.mul, F.add
        out = {self.norm(x)}
        for s in F.elts():
            out.add(self.norm([A[M[s][a]][b] for a, b in zip(x, y)]))
        return out
    def nullspace(self, rows):
        F = self.F; M, A, S, inv = F.mul, F.add, F.sub, F.inv
        R = [list(r) for r in rows]; n = 7; piv = []; r = 0
        for c in range(n):
            pr = next((k for k in range(r, len(R)) if R[k][c]), None)
            if pr is None: continue
            R[r], R[pr] = R[pr], R[r]
            ic = inv[R[r][c]]; R[r] = [M[ic][t] for t in R[r]]
            for k in range(len(R)):
                if k != r and R[k][c]:
                    f = R[k][c]; R[k] = [S[a][M[f][b]] for a, b in zip(R[k], R[r])]
            piv.append(c); r += 1
        free = [c for c in range(n) if c not in piv]
        basis = []
        for fc in free:
            v = [0] * n; v[fc] = 1
            for k, pc in enumerate(piv): v[pc] = S[0][R[k][fc]]
            basis.append(v)
        return basis
    def line_of(self, x, y):
        return self.lid[frozenset(self.pid[p] for p in self.span_pts(x, y))]
    def incidence_edges(self):
        N = self.N
        return [(i, N + k) for k, L in enumerate(self.lines) for i in L]
def write_edges(fn, n, edges):
    with open(fn, 'w') as f:
        f.write(f"{n} {len(edges)}\n" + "\n".join(f"{u} {v}" for u, v in edges) + "\n")
