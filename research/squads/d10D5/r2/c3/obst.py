"""obst.py: flag-set model of flagmatch.py / flaggreedy.py with bitsets, Hall-violator extraction and
pair/triple intersection statistics.  Points x, lines M: edge (x, M) allowed iff M in Ll_i for every flag i with
x in A_i, and x in Pp_i for every flag i with M in G_i; freed points/lines are fixed to their partner.
A flag is (p, l) with p on l.  A_i = P[p]\\l (49), Ll_i = L[l]\\{l} (56), G_i = L[l]\\thr(p) (49), Pp_i = P[p]\\{p} (56)."""
import sys
sys.setrecursionlimit(20000)
sys.path.insert(0, '.')
from gq import load, perp, lperp

class Geo:
    def __init__(self, fn='gq/gq_q7.bin'):
        self.q, self.N, self.lines, self.lof = load(fn)
        N = self.N
        self.Pm = [sum(1 << y for y in perp(self.lines, self.lof, p)) for p in range(N)]
        self.Lm = [sum(1 << m for m in lperp(self.lines, self.lof, l)) for l in range(N)]
        self.onl = [sum(1 << y for y in self.lines[l]) for l in range(N)]
        self.thr = [sum(1 << m for m in self.lof[p]) for p in range(N)]
        self.ALL = (1 << N) - 1
        self.ptsof = [list(self.lines[l]) for l in range(N)]

    def flag_sets(self, p, l):
        A = self.Pm[p] & ~self.onl[l]; G = self.Lm[l] & ~self.thr[p]
        Ll = self.Lm[l] & ~(1 << l); Pp = self.Pm[p] & ~(1 << p)
        return A, Ll, G, Pp

    def matching(self, flags, want_violator=False):
        """flags: list of (p, l).  Returns (size, matchL, violator) ; deficiency = N - size."""
        N = self.N; ALL = self.ALL
        F = {p: l for p, l in flags}; Fl = {l: p for p, l in flags}
        Fm = sum(1 << p for p in F); Flm = sum(1 << l for l in Fl)
        lineok = [ALL & ~Flm] * N; ptok = [ALL & ~Fm] * N
        for p, l in flags:
            A, Ll, G, Pp = self.flag_sets(p, l)
            x = A
            while x:
                b = x & -x; i = b.bit_length() - 1; lineok[i] &= Ll; x ^= b
            m = G
            while m:
                b = m & -m; i = b.bit_length() - 1; ptok[i] &= Pp; m ^= b
        adj = []
        for x in range(N):
            if x in F: adj.append([F[x]]); continue
            row = []; m = lineok[x]
            while m:
                b = m & -m; M = b.bit_length() - 1; m ^= b
                if ptok[M] >> x & 1: row.append(M)
            adj.append(row)
        matchR = [-1] * N; matchL = [-1] * N
        for p, l in flags: matchR[l] = p; matchL[p] = l
        for u in range(N):
            if matchL[u] >= 0: continue
            # greedy first
            for v in adj[u]:
                if matchR[v] < 0: matchR[v] = u; matchL[u] = v; break
        def aug(u, seen):
            for v in adj[u]:
                if seen[v]: continue
                seen[v] = True
                if matchR[v] < 0 or aug(matchR[v], seen):
                    matchR[v] = u; matchL[u] = v; return True
            return False
        for u in range(N):
            if matchL[u] < 0:
                aug(u, [False] * N)
        size = sum(1 for u in range(N) if matchL[u] >= 0)
        viol = None
        if want_violator and size < N:
            # alternating BFS from unmatched left vertices
            Zl = set(u for u in range(N) if matchL[u] < 0); Zr = set(); stack = list(Zl)
            while stack:
                u = stack.pop()
                for v in adj[u]:
                    if v in Zr: continue
                    Zr.add(v)
                    w = matchR[v]
                    if w >= 0 and w not in Zl: Zl.add(w); stack.append(w)
            viol = (sorted(Zl), sorted(Zr))
        return size, matchL, viol

def pair_triple_stats(geo, flags):
    """intersection sizes for pairs and triples of flags, for the four families"""
    sets = [geo.flag_sets(p, l) for p, l in flags]
    out = {}
    import itertools
    names = ['A', 'Ll', 'G', 'Pp']
    for r in (2, 3):
        for S in itertools.combinations(range(len(flags)), r):
            vals = []
            for f in range(4):
                m = sets[S[0]][f]
                for s in S[1:]: m &= sets[s][f]
                vals.append(bin(m).count('1'))
            out[S] = dict(zip(names, vals))
    return out

def describe(geo, flags):
    size, mL, viol = geo.matching(flags, want_violator=True)
    return size, mL, viol

if __name__ == '__main__':
    import time
    geo = Geo()
    flags = [tuple(map(int, t.split(':'))) for t in sys.argv[1:]]
    t0 = time.time()
    size, mL, viol = describe(geo, flags)
    print('k', len(flags), 'matching', size, 'of', geo.N, 'deficiency', geo.N - size, 'time %.2f' % (time.time() - t0))
    if viol:
        X, NX = viol
        print('violator: |X| =', len(X), '|N(X)| =', len(NX))
    st = pair_triple_stats(geo, flags)
    for S, d in st.items():
        print(S, d)
