# e03: build solvable groups of order 1152 and 1200 (not in round 1), as tables for haar_tab.
import sys, itertools, random
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/tools")
import numpy as np
import groups as G

def closure_size(gens, n, limit=5000):
    ident = tuple(range(n)); seen = {ident}; frontier = [ident]
    while frontier:
        g = frontier.pop()
        for s in gens:
            h = tuple(g[s[t]] for t in range(n))
            if h not in seen:
                seen.add(h); frontier.append(h)
                if len(seen) > limit: return limit + 1
    return len(seen)

def perm_of_affine(M, t, p, base):
    # points: vectors over Z_p of length d, index = sum x_i base^i ; map x -> M x + t
    d = len(t)
    pts = list(itertools.product(range(p), repeat=d))  # index order: first coord slowest
    idx = {v: i for i, v in enumerate(pts)}
    out = []
    for v in pts:
        w = tuple((sum(M[i][j] * v[j] for j in range(d)) + t[i]) % p for i in range(d))
        out.append(idx[w])
    return tuple(out)

def mat_perm(M, p):
    return perm_of_affine(M, [0] * len(M), p, None)

def tab_perm(n, gens):
    return G.t_perm(n, gens)

def tp(*tabs):
    T = tabs[0]
    for U in tabs[1:]:
        T = G.t_prod(T, U)
    return T

def dump(name, T, order):
    assert len(T) == order, (name, len(T), order)
    G.check(T)
    G.write_bin(T, f"/home/user/degree-diameter/research/squads/b48/r3/e03/{name}.bin")
    inv = sum(1 for g in range(len(T)) if g and T[g, g] == 0)
    print(f"{name} N={len(T)} involutions={inv}", flush=True)

def gl2_gens(p):
    return [[[0, 1], [1, 0]], [[1, 1], [0, 1]], [[1, 0], [0, 2 if p == 3 else 2]]]

out = sys.argv[1:] or ["all"]
which = out[0]

# ---- order 1152 ----
# A1: AGammaL(1,9) = Z3^2 x| SD16 (Sylow-2 of GL(2,3)), times Z8
def find_subgroup_gl23(order):
    mats = []
    for a, b, c, d in itertools.product(range(3), repeat=4):
        if (a * d - b * c) % 3: mats.append(((a, b), (c, d)))
    def mul(X, Y):
        return tuple(tuple(sum(X[i][k] * Y[k][j] for k in range(2)) % 3 for j in range(2)) for i in range(2))
    def gen_closure(gs):
        S = {((1, 0), (0, 1))}; fr = list(S)
        while fr:
            x = fr.pop()
            for g in gs:
                y = mul(x, g)
                if y not in S: S.add(y); fr.append(y)
        return frozenset(S)
    for X in mats:
        for Y in mats:
            S = gen_closure([X, Y])
            if len(S) == order:
                return sorted(S), [X, Y]
    raise SystemExit("no subgroup")

def translations_perm(p, d):
    gens = []
    for i in range(d):
        t = [0] * d; t[i] = 1
        gens.append(perm_of_affine([[1 if r == c else 0 for c in range(d)] for r in range(d)], t, p, None))
    return gens

def affine_group_perm(p, d, mats):
    # translations + linear generators (as affine perms) on p^d points
    gens = translations_perm(p, d)
    for M in mats:
        gens.append(perm_of_affine(M, [0] * d, p, None))
    return gens

if which in ("all", "A1"):
    S, gs = find_subgroup_gl23(16)
    gens = affine_group_perm(3, 2, [list(map(list, g)) for g in gs])
    T16 = tab_perm(9, gens)  # Z3^2 x| SD16 acting on 9 points -- order should be 144
    T = tp(T16, G.table("cyc 8"))
    dump("A1_AGaL19_x_Z8", T, 1152)

# A2: Z2^4 x| (Z3 x Z3) (F4^2 as F2^4) times Z8
if which in ("all", "A2"):
    # F4 mult by w on F2^2 (basis 1,w): w*1=w, w*w=1+w
    W = [[0, 1], [1, 1]]
    I2 = [[1, 0], [0, 1]]
    def blk(A, B):
        Z = [[0]*4 for _ in range(4)]
        for i in range(2):
            for j in range(2):
                Z[i][j] = A[i][j]; Z[i+2][j+2] = B[i][j]
        return Z
    m1 = blk(W, I2); m2 = blk(I2, W)
    gens = affine_group_perm(2, 4, [m1, m2])
    T144 = tab_perm(16, gens)
    dump_T = tp(T144, G.table("cyc 8"))
    dump("A2_Z2^4_x_Z3^2_x_Z8", dump_T, 1152)

# A5: GL(2,3) x Z24 (perm on 9 points)
if which in ("all", "A5"):
    gens = [perm_of_affine(M, [0, 0], 3, None) for M in [[[0, 1], [1, 0]], [[1, 1], [0, 1]], [[1, 0], [0, 2]], [[2, 0], [0, 1]]]]
    gl = tab_perm(9, gens)
    dump("A5_GL23_x_Z24", tp(gl, G.table("cyc 24")), 1152)

# A3: A4 x A4 x Z8
if which in ("all", "A3"):
    a4 = tab_perm(4, [(1, 2, 0, 3), (1, 0, 3, 2)])
    dump("A3_A4xA4xZ8", tp(a4, a4, G.table("cyc 8")), 1152)

# A6: S3 x S3 x Z4 x Z8  (order 1152)
if which in ("all", "A6"):
    dump("A6_S3xS3xZ4xZ8", tp(G.table("dih 3"), G.table("dih 3"), G.table("cyc 4"), G.table("cyc 8")), 1152)

# ---- order 1200 ----
def F25():
    # elements a + b i, i^2 = 2, index a + 5 b
    def mul(x, y):
        a, b = x % 5, x // 5 % 5
        c, d = y % 5, y // 5 % 5
        return ((a*c + 2*b*d) % 5) + 5 * ((a*d + b*c) % 5)
    return mul

if which in ("all", "B2", "B1", "B3"):
    mul = F25()
    def power(x, k):
        r = 1
        for _ in range(k): r = mul(r, x)
        return r
    # generator of F25^* (order 24)
    g = next(x for x in range(1, 25) if all(power(x, 24 // q) != 1 for q in (2, 3)))
    tr1 = [(x + 1) % 5 + 5 * (x // 5) for x in range(25)]  # x -> x+1
    tri = [ (x + 5) % 25 for x in range(25)]  # x -> x+i (a + b i + i)
    tri = [ ((x % 5)) + 5 * ((x // 5 + 1) % 5) for x in range(25)]
    mg = [mul(g, x) for x in range(25)]
    frob = [power(x, 5) for x in range(25)]
    # B2: A GammaL(1,25) = F25 x| (Z24 x| Z2)
    gens = [tuple(tr1), tuple(tri), tuple(mg), tuple(frob)]
    if which in ("all", "B2"):
        Tb2 = tab_perm(25, gens)
        dump("B2_AGammaL125", Tb2, 1200)
    # matrices of GL(2,5) for B1/B3 on the 25 points of F5^2 (index x + 5y)
    def sl23_pair():
        mats = []
        for a, b, c, d in itertools.product(range(5), repeat=4):
            if (a*d - b*c) % 5 == 1: mats.append(((a, b), (c, d)))
        def mm(X, Y):
            return tuple(tuple(sum(X[i][k]*Y[k][j] for k in range(2)) % 5 for j in range(2)) for i in range(2))
        def clos(gs, cap=30):
            S = {((1,0),(0,1))}; fr = list(S)
            while fr:
                x = fr.pop()
                for h in gs:
                    y = mm(x, h)
                    if y not in S:
                        S.add(y); fr.append(y)
                        if len(S) > cap: return None
            return S
        random.seed(5)
        for _ in range(200000):
            A = random.choice(mats); B = random.choice(mats)
            S = clos([A, B])
            if S is not None and len(S) == 24:
                # need a non-abelian group with element of order 3 and 4 (binary tetrahedral)
                return A, B, S
        raise SystemExit("no SL23")
    A, B, S = sl23_pair()
    def lin_perm(M):
        return perm_of_affine(M, [0, 0], 5, None)
    trans = [lin_perm([[1, 0], [0, 1]])]  # placeholder, replaced below
    tr = translations_perm(5, 2)
    if which in ("all", "B3"):
        sl = [lin_perm(A), lin_perm(B)]
        Tb3 = tab_perm(25, tr + sl)
        dump("B3_Z5^2_x_SL23_x_Z2", tp(Tb3, G.table("cyc 2")), 1200)
    if which in ("all", "B1"):
        sc = lin_perm([[2, 0], [0, 2]])   # scalar 2 (order 4 in F5^*)
        Tb1 = tab_perm(25, tr + [lin_perm(A), lin_perm(B), sc])
        dump("B1_Z5^2_x_(SL23o4)", Tb1, 1200)

if which in ("all", "B4"):
    a5 = tab_perm(5, [(1, 2, 3, 4, 0), (1, 2, 0, 3, 4)])
    f20 = tab_perm(5, [(1, 2, 3, 4, 0), (0, 2, 4, 1, 3)])
    dump("B4_A5_x_F20", tp(a5, f20), 1200)
