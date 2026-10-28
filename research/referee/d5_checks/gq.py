"""W(q) from the symplectic form of the note (sec. 1.2) and Q(4,q) built directly from the quadric
X0X1 + X2^2 + X3X4 = 0 (not as the dual of W(q)), for the referee checks."""
import itertools
from gf import GF, normalize, proj_points, span_points

class GQ:
    """points 0..N-1, lines 0..N-1, pl[p] = lines on p, lp[l] = points on l"""
    def __init__(self, lp, npts):
        self.lp = [sorted(l) for l in lp]
        self.N = npts
        self.pl = [[] for _ in range(npts)]
        for i, l in enumerate(self.lp):
            for p in l:
                self.pl[p].append(i)
        self.collinear = [set() for _ in range(npts)]   # Gamma_2 of points
        for l in self.lp:
            for a in l:
                for b in l:
                    if a != b:
                        self.collinear[a].add(b)
        self.meets = [set() for _ in range(len(lp))]    # Gamma_2 of lines
        for p in range(npts):
            for a in self.pl[p]:
                for b in self.pl[p]:
                    if a != b:
                        self.meets[a].add(b)

    def dual(self):
        return GQ(self.pl, len(self.lp))

    def check_axioms(self, s, t):
        assert len(self.lp) == (t + 1) * (s * t + 1) and self.N == (s + 1) * (s * t + 1)
        assert all(len(l) == s + 1 for l in self.lp) and all(len(x) == t + 1 for x in self.pl)
        for i, l in enumerate(self.lp):
            ls = set(l)
            for p in range(self.N):
                if p in ls:
                    continue
                k = len(self.collinear[p] & ls)
                assert k == 1, (p, i, k)
        return True

def W(F):
    q = F.q
    pts = proj_points(F, 4)
    idx = {p: i for i, p in enumerate(pts)}
    def w(x, y):
        m = F.mul; a = F.add
        return F.sub[a[m[x[0]][y[2]]][m[x[1]][y[3]]]][a[m[x[2]][y[0]]][m[x[3]][y[1]]]]
    lines = set()
    for x in pts:
        covered = {x}
        for y in pts:
            if y not in covered and w(x, y) == 0:
                S = span_points(F, x, y)
                covered |= S
                lines.add(frozenset(idx[z] for z in S))
    lines = sorted(sorted(l) for l in lines)
    G = GQ(lines, len(pts))
    G.coords = pts; G.idx = idx; G.form = w
    return G

def Q4(F):
    """points of X0X1+X2^2+X3X4=0 in PG(4,q); lines = projective lines all of whose points lie on it"""
    m, a = F.mul, F.add
    def Q(X):
        return a[a[m[X[0]][X[1]]][m[X[2]][X[2]]]][m[X[3]][X[4]]]
    pts = [X for X in proj_points(F, 5) if Q(X) == 0]
    idx = {p: i for i, p in enumerate(pts)}
    def Bf(X, Y):   # polar form X0Y1+X1Y0+2X2Y2+X3Y4+X4Y3
        t = a[a[m[X[0]][Y[1]]][m[X[1]][Y[0]]]][a[m[X[3]][Y[4]]][m[X[4]][Y[3]]]]
        return a[t][a[m[X[2]][Y[2]]][m[X[2]][Y[2]]]]
    lines = set()
    for x in pts:
        covered = {x}
        for y in pts:
            if y not in covered and Bf(x, y) == 0:
                S = span_points(F, x, y)
                assert all(Q(z) == 0 for z in S)
                covered |= S
                lines.add(frozenset(idx[z] for z in S))
    lines = sorted(sorted(l) for l in lines)
    G = GQ(lines, len(pts))
    G.coords = pts; G.idx = idx; G.Q = Q
    return G

def plucker(F, x, y):
    """p_ij = x_i y_j - x_j y_i, returned as dict"""
    m, s = F.mul, F.sub
    return {(i, j): s[m[x[i]][y[j]]][m[x[j]][y[i]]] for i in range(4) for j in range(i + 1, 4)}

if __name__ == "__main__":
    for q in (2, 3, 4, 5, 7):
        F = GF(q)
        Wq = W(F); Qq = Q4(F)
        Wq.check_axioms(q, q); Qq.check_axioms(q, q)
        # Klein correspondence of sec. 1.2: line <x,y> of W(q) -> (p01,p23,p02,p03,p12) is a point of Q(4,q),
        # pencils go to lines; so this map is an isomorphism W(q)^D -> Q(4,q)
        img = []
        for l in Wq.lp:
            x, y = Wq.coords[l[0]], Wq.coords[l[1]]
            P = plucker(F, x, y)
            assert F.add[P[(0, 2)]][P[(1, 3)]] == 0           # p02 + p13 = 0 on isotropic lines
            X = normalize(F, (P[(0, 1)], P[(2, 3)], P[(0, 2)], P[(0, 3)], P[(1, 2)]))
            img.append(Qq.idx[X])
        assert len(set(img)) == Qq.N
        for p in range(Wq.N):
            pencil = sorted(img[l] for l in Wq.pl[p])
            assert pencil in Qq.lp
        print("q=%d: W(q), Q(4,q) GQ axioms ok; Klein map W(q)^D -> Q(4,q) is an isomorphism" % q)
