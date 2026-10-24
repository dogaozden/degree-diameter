r"""Predicted distance distribution of the bipartite flag graph of a spherical building, from the Weyl group alone
(BUILDINGS.md, Theorem 1 and its distance formula).

Vertices: flags of type I1 and flags of type I2 (I1 | I2 = the two colour classes of the Coxeter diagram); a flag of
type X is a residue of type S\X.  For a vertex R that is a residue of type J and w in W put
    m_J(w) = least m with w in W_J W_J' W_J ... (m alternating factors, the first one W_J),
    J_m    = type of the m-th factor (J if m odd, J' if m even),
    d_JK(w) = m_J(w) - [J_m == K].
Then a residue R' of type K with delta(R,R') = W_J w W_K is at distance d_JK(w) from R, and the number of
K-residues at distance d from R is   (1/P_K) * sum_{w : d_JK(w) = d} q_w ,   P_K = sum_{u in W_K} q_u.
q_w = prod of the parameters q_s along a reduced word (one parameter per conjugacy class of simple reflections).

Weyl group as orbit of rho = (1,..,1) (fundamental-weight coordinates, integer Cartan matrix); lengths and
class-lengths by BFS with single reflections; m_J by a block BFS (left multiplication, using w <-> w^-1).
usage: python3 weyl_dist.py TYPE RANK q1[,q2]     e.g.  A 4 3   |  B 3 2,4   (q per class: B/C/F: short..)"""
import sys
from collections import defaultdict

def cartan(t, n):
    C = [[2 if i == j else 0 for j in range(n)] for i in range(n)]
    def bond(i, j, a=-1, b=-1): C[i][j] = a; C[j][i] = b
    if t == 'A':
        for i in range(n - 1): bond(i, i + 1)
    elif t in 'BC':
        for i in range(n - 2): bond(i, i + 1)
        bond(n - 2, n - 1, -2, -1)
    elif t == 'D':
        for i in range(n - 3): bond(i, i + 1)
        bond(n - 3, n - 2); bond(n - 3, n - 1)
    elif t == 'E':
        ch = [0, 2] + list(range(3, n))
        for a, b in zip(ch, ch[1:]): bond(a, b)
        bond(1, 3)
    elif t == 'F':
        bond(0, 1); bond(1, 2, -2, -1); bond(2, 3)
    elif t == 'G':
        bond(0, 1, -3, -1)
    return C

def classes_of_reflections(C):
    """simple reflections s_i, s_j are conjugate iff joined by a path of odd bonds (m_ij odd, i.e. C_ij C_ji = 1)."""
    n = len(C); lab = list(range(n))
    def find(x):
        while lab[x] != x: x = lab[x]
        return x
    for i in range(n):
        for j in range(n):
            if i != j and C[i][j] * C[j][i] == 1: lab[find(i)] = find(j)
    roots = sorted({find(i) for i in range(n)})
    return [roots.index(find(i)) for i in range(n)]

def weyl(C):
    n = len(C)
    col = [[C[j][i] for j in range(n)] for i in range(n)]      # alpha_i in omega-coordinates
    def s(i, lam):
        a = lam[i]
        return tuple(x - a * y for x, y in zip(lam, col[i]))
    return s

def colour(C):
    n = len(C); c = [-1] * n; c[0] = 0; st = [0]
    while st:
        x = st.pop()
        for y in range(n):
            if y != x and C[x][y] != 0 and c[y] < 0: c[y] = 1 - c[x]; st.append(y)
    return [[i for i in range(n) if c[i] == k] for k in (0, 1)]

def analyse(t, n):
    C = cartan(t, n); s = weyl(C); cls = classes_of_reflections(C); ncls = max(cls) + 1
    rho = tuple([1] * n)
    # BFS by single reflections (left multiplication): length and class-length vector
    info = {rho: (0,) * ncls}; frontier = [rho]
    while frontier:
        nf = []
        for lam in frontier:
            L = info[lam]
            for i in range(n):
                if lam[i] > 0:            # s_i w longer than w  iff  <w rho, alpha_i^vee> > 0
                    mu = s(i, lam)
                    if mu not in info:
                        v = list(L); v[cls[i]] += 1; info[mu] = tuple(v); nf.append(mu)
        frontier = nf
    I = colour(C)
    # block BFS for each starting class J: level[J][w] = least m with w^-1 in W_{J_m}...W_{J_1} (left mult.)
    level = []
    for J in (0, 1):
        lev = {rho: 1}
        # level 1 = W_J (orbit of rho under the commuting reflections of class J)
        def block(lam, K):
            orb = {lam}
            for i in I[K]:
                orb |= {s(i, x) for x in orb}
            return orb
        frontier = []
        for x in block(rho, J):
            if x not in lev: lev[x] = 1
            frontier.append(x)
        frontier = [x for x in frontier]
        m = 1
        while frontier:
            m += 1; K = J if m % 2 == 1 else 1 - J; nf = []
            for lam in frontier:
                for x in block(lam, K):
                    if x not in lev: lev[x] = m; nf.append(x)
            frontier = nf
        assert len(lev) == len(info)
        level.append(lev)
    return C, I, cls, ncls, info, level

def polymul(a, b):
    r = defaultdict(int)
    for ea, ca in a.items():
        for eb, cb in b.items(): r[tuple(x + y for x, y in zip(ea, eb))] += ca * cb
    return r

def predict(t, n, params):
    C, I, cls, ncls, info, level = analyse(t, n)
    if len(params) == 1: params = params * ncls
    assert len(params) == ncls, f"need {ncls} parameters (one per reflection class), got {len(params)}"
    qw = lambda L: eval_mono(L, params)
    E = sum(qw(L) for L in info.values())
    out = {}
    for J in (0, 1):                 # source vertex = residue of type I[J] = flag of type I[1-J]
        for K in (0, 1):             # target vertex = residue of type I[K]
            PK = 1
            for i in I[K]: PK *= (1 + params[cls[i]])
            cnt = defaultdict(int)
            for lam, L in info.items():
                m = level[J][lam]
                Jm = J if m % 2 == 1 else 1 - J
                d = m - (1 if Jm == K else 0)
                cnt[d] += qw(L)
            for d in cnt: assert cnt[d] % PK == 0
            out[(J, K)] = {d: cnt[d] // PK for d in sorted(cnt)}
    return C, I, cls, E, out, len(info), params

def eval_mono(L, params):
    v = 1
    for e, q in zip(L, params): v *= q ** e
    return v

if __name__ == '__main__':
    t, n = sys.argv[1], int(sys.argv[2]); params = [int(x) for x in sys.argv[3].split(',')]
    C, I, cls, E, out, W, params = predict(t, n, params)
    print(f"type {t}{n}, |W| = {W}, classes I1={I[0]} I2={I[1]} (0-based nodes), reflection classes {cls}, params {params}")
    print(f"chambers {E}")
    for J in (0, 1):
        deg = 1
        for i in I[J]: deg *= 1 + params[cls[i]]
        nv = E // deg
        print(f" source: residue of type I{J+1} (a flag of type I{2-J}), degree {deg}, {nv} such vertices")
        for K in (0, 1):
            print(f"   targets of residue type I{K+1}: " + ", ".join(f"d={d}:{c}" for d, c in out[(J, K)].items()))
        ecc = max(max(out[(J, 0)]), max(out[(J, 1)]))
        print(f"   eccentricity {ecc}")
