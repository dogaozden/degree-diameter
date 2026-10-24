"""Route charts over F_q^n and the reachable sets of lifted walks (bipartite route-chart lift, CHART_LIFTS.md).

Lift of a properly k-edge-coloured bipartite controller C (sides A, B): vertex (u, x), x in F_q^n; a controller edge
u -- v (u in A, v in B) of colour c gives (u, x) ~ (v, A_c x + lam b_c), lam in F_q.  Degree k q, order |C| q^n.
A step A->B along colour c maps an affine set M x + S to A_c M x + (A_c S + <b_c>); a step B->A maps it to
A_c^-1 M x + (A_c^-1 S + <w_c>), w_c = A_c^-1 b_c.  Everything below is computed from these two rules."""
import itertools
from gf import GF

class Chart:
    def __init__(self, q, A, b):
        self.F = F = GF(q) if isinstance(q, int) else q
        self.q = F.q; self.k = len(A); self.n = len(b[0])
        self.A = [tuple(tuple(r) for r in M) for M in A]; self.b = [tuple(v) for v in b]
        self.Ai = [F.matinv(M) for M in self.A]
        assert all(M is not None for M in self.Ai), 'singular A_c'
        assert all(any(v) for v in self.b), 'zero b_c'
        self.w = [F.matvec(self.Ai[c], self.b[c]) for c in range(self.k)]
        self.full = self.q ** self.n

    # ---- reachable sets of walks ----------------------------------------------------------------------------------
    def walk(self, start_side, colours):
        """start_side 'A' or 'B'; returns (M, basis list) with reach(x) = M x + span(basis)."""
        F, n = self.F, self.n
        M = tuple(tuple(int(r == c) for c in range(n)) for r in range(n)); S = []
        side = start_side
        for c in colours:
            if side == 'A':
                M = F.matmul(self.A[c], M); S = [F.matvec(self.A[c], v) for v in S] + [self.b[c]]; side = 'B'
            else:
                M = F.matmul(self.Ai[c], M); S = [F.matvec(self.Ai[c], v) for v in S] + [self.w[c]]; side = 'A'
        return M, S

    def rank(self, S): return self.F.rank(S) if S else 0

    def nb_patterns(self, L=None):
        L = L or self.n; k = self.k
        for pat in itertools.product(range(k), repeat=L):
            if all(pat[t] != pat[t + 1] for t in range(L - 1)): yield pat

    def singular_patterns(self, L=None):
        """list of (side, pattern, rank) for nonbacktracking walks of length L (default n) with rank < n"""
        out = []
        for side in 'AB':
            for pat in self.nb_patterns(L):
                r = self.rank(self.walk(side, pat)[1])
                if r < self.n: out.append((side, pat, r))
        return out

    def _union_covers(self, spans):
        F, n = self.F, self.n; cov = set()
        for S in spans: cov |= F.span(S, n)
        return len(cov), len(cov) == self.full

    # ---- distance-2 pairs (D = 5): one-detour walks through the common neighbour -----------------------------------
    def pencil_walks(self, side, i, j):
        """colour patterns of the length-4 walks u -> u' that backtrack once, u, u' on `side`, common neighbour via
        colours i (u side) and j (u' side): a detour of colour t at u, at the middle vertex, or at u'."""
        k = self.k; pats = []
        for t in range(k):
            pats.append((t, t, i, j)); pats.append((i, t, t, j)); pats.append((i, j, t, t))
        return pats

    def pencil(self, side, i, j):
        spans = [self.walk(side, p)[1] for p in self.pencil_walks(side, i, j)]
        Ms = {self.walk(side, p)[0] for p in self.pencil_walks(side, i, j)}
        assert len(Ms) == 1           # same linear part: the union is translation-invariant
        return self._union_covers(spans)

    def pencil_report(self):
        bad = []
        for side in 'AB':
            for i in range(self.k):
                for j in range(self.k):
                    if i != j:
                        cnt, ok = self.pencil(side, i, j)
                        if not ok: bad.append((side, i, j, cnt))
        return bad

    # ---- diagonal pairs (u, u): closed walks of length 4 --------------------------------------------------------
    def closed_backtrack_walks(self):
        k = self.k; pats = set()
        for s in range(k):
            for t in range(k):
                pats.add((s, s, t, t)); pats.add((s, t, t, s))
        return sorted(pats)

    def diagonal(self, side):
        spans = [self.walk(side, p)[1] for p in self.closed_backtrack_walks()]
        return self._union_covers(spans)

    def cycle_patterns(self):
        """closed nonbacktracking colour patterns of length 4 (4-cycles), with their rank on each side"""
        out = []
        for pat in self.nb_patterns(4):
            if pat[3] != pat[0]:
                out.append((pat, self.rank(self.walk('A', pat)[1]), self.rank(self.walk('B', pat)[1])))
        return out

    def summary(self):
        sing = self.singular_patterns()
        pb = self.pencil_report()
        dA, dB = self.diagonal('A'), self.diagonal('B')
        return {'k': self.k, 'q': self.q, 'singular': len(sing), 'singular_list': sing, 'pencil_fail': pb,
                'diagA': dA, 'diagB': dB, 'perfect': not sing and not pb and dA[1] and dB[1]}

def read_chart_txt(path, q, k=4, n=4):
    """chart file format of squad165/charts/*.txt: k lines of n*n entries (A_c row-major), then k lines of b_c"""
    vals = [list(map(int, line.split())) for line in open(path) if line.strip()]
    A = [tuple(tuple(r[t * n:(t + 1) * n]) for t in range(n)) for r in vals[:k]]
    b = [tuple(r) for r in vals[k:2 * k]]
    return Chart(q, A, b)

def write_chart_txt(ch, path):
    with open(path, 'w') as f:
        for M in ch.A: f.write(' '.join(str(x) for row in M for x in row) + '\n')
        for v in ch.b: f.write(' '.join(map(str, v)) + '\n')
