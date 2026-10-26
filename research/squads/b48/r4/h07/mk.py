# Build permutation groups of order 802..900 (even, index-2 subgroup) as multiplication tables.
# Usage: python3 mk.py NAME  -> writes NAME.tab (first line N, then N rows of N ints, identity = 0)
import sys, itertools, random

def mul(p, q):  # (p o q)(i) = p[q[i]]
    return tuple(p[i] for i in q)

def closure(gens, P):
    idp = tuple(range(P))
    elems = [idp]; index = {idp: 0}
    frontier = [idp]
    while frontier:
        new = []
        for p in frontier:
            for g in gens:
                q = mul(p, g)
                if q not in index:
                    index[q] = len(elems); elems.append(q); new.append(q)
        frontier = new
    return elems, index

def table(gens, P):
    elems, index = closure(gens, P)
    N = len(elems)
    import numpy as np
    E = np.array(elems, dtype=np.int64)
    rows = []
    # T[i][j] = index(e_i o e_j); use bytes keys
    keys = {}
    for k, e in enumerate(elems):
        keys[np.array(e, dtype=np.int16).tobytes()] = k
    T = np.zeros((N, N), dtype=np.int64)
    for i in range(N):
        pi = E[i]
        prod = pi[E].astype(np.int16)  # row j: pi[e_j[t]]
        for j in range(N):
            T[i, j] = keys[prod[j].tobytes()]
    return N, T

def cyc(n, start, cycles):
    p = list(range(n))
    return p

def perm_from_cycles(P, cycles):
    p = list(range(P))
    for c in cycles:
        for a, b in zip(c, c[1:] + c[:1]):
            p[a] = b
    return tuple(p)

def shift(gens, off, P):
    # embed perms on a block of size len into P points at offset off
    out = []
    for g, blk in gens:
        p = list(range(P))
        for i, v in enumerate(g):
            p[off + i] = off + v
        out.append(tuple(p))
    return out

def direct(*factors):
    # factors: list of (gens, size)
    P = sum(s for _, s in factors)
    allg = []
    off = 0
    for gens, s in factors:
        allg += shift([(g, s) for g in gens], off, P)
        off += s
    return allg, P

def dih(n):
    rot = tuple((i + 1) % n for i in range(n))
    ref = tuple((-i) % n for i in range(n))
    return [rot, ref], n

def cycg(n):
    return [tuple((i + 1) % n for i in range(n))], n

def sym(n):
    t = perm_from_cycles(n, [(0, 1)])
    c = perm_from_cycles(n, [tuple(range(n))])
    return [t, c], n

def alt(n):
    return [perm_from_cycles(n, [(0, 1, 2)]), perm_from_cycles(n, [tuple(range(n))]) if n % 2 else perm_from_cycles(n, [tuple(range(n-1))])], n

def A5():
    return [perm_from_cycles(5, [(0, 1, 2)]), perm_from_cycles(5, [(0, 1, 2, 3, 4)])], 5

def A4():
    return [perm_from_cycles(4, [(0, 1, 2)]), perm_from_cycles(4, [(0, 1), (2, 3)])], 4

def S4():
    return [perm_from_cycles(4, [(0, 1)]), perm_from_cycles(4, [(0, 1, 2, 3)])], 4

def S5():
    return [perm_from_cycles(5, [(0, 1)]), perm_from_cycles(5, [(0, 1, 2, 3, 4)])], 5

# linear maps on F_p^k acting on vectors; points indexed by base-p digits
def vec_index(v, p):
    idx = 0
    for x in v:
        idx = idx * p + (x % p)
    return idx

def all_vecs(k, p):
    return list(itertools.product(range(p), repeat=k))

def linear_perm(M, p, k):
    pts = all_vecs(k, p)
    perm = [0] * (p ** k)
    for v in pts:
        w = tuple(sum(M[r][c] * v[c] for c in range(k)) % p for r in range(k))
        perm[vec_index(v, p)] = vec_index(w, p)
    return tuple(perm)

def translation(b, p, k):
    pts = all_vecs(k, p)
    perm = [0] * (p ** k)
    for v in pts:
        w = tuple((v[i] + b[i]) % p for i in range(k))
        perm[vec_index(v, p)] = vec_index(w, p)
    return tuple(perm)

def affine(p, k, Ms):
    gens = [translation([1 if i == j else 0 for i in range(k)], p, k) for j in range(k)]
    gens += [linear_perm(M, p, k) for M in Ms]
    return gens, p ** k

def gl23_gens():
    return [[[1, 1], [0, 1]], [[0, 1], [1, 0]], [[2, 0], [0, 1]]]

def sd16_in_gl23():
    # find a subgroup of GL(2,3) of order 16 consisting of 2-elements
    p = 3
    mats = []
    for a, b, c, d in itertools.product(range(3), repeat=4):
        if (a * d - b * c) % 3:
            mats.append(((a, b), (c, d)))
    def mm(X, Y):
        return tuple(tuple(sum(X[i][k] * Y[k][j] for k in range(2)) % 3 for j in range(2)) for i in range(2))
    I = ((1, 0), (0, 1))
    def order(X):
        k, Y = 1, X
        while Y != I:
            Y = mm(Y, X); k += 1
        return k
    two = [X for X in mats if order(X) in (1, 2, 4, 8)]
    for X in two:
        for Y in two:
            G = {I}; fr = [I]
            while fr:
                nf = []
                for Z in fr:
                    for g in (X, Y):
                        W = mm(Z, g)
                        if W not in G:
                            G.add(W); nf.append(W)
                fr = nf
                if len(G) > 16:
                    break
            if len(G) == 16:
                return [X, Y]
    raise SystemExit("no SD16")

def build(name):
    if name == 'A5xD7':
        g, P = direct((A5()[0], 5), (dih(7)[0], 7)) if False else (None, None)
        gA = [perm_from_cycles(12, [(0, 1, 2)]), perm_from_cycles(12, [(0, 1, 2, 3, 4)])]
        gD = [perm_from_cycles(12, [tuple(range(5, 12))]), tuple([0,1,2,3,4]+[5+((-i)%7) for i in range(7)])]
        gens = gA + [tuple(list(range(5)) + [5 + ((i+1) % 7) for i in range(7)]), tuple(list(range(5)) + [5 + ((-i) % 7) for i in range(7)])]
        return gens, 12
    if name == 'S5xZ7':
        gens = [perm_from_cycles(12, [(0, 1)]), perm_from_cycles(12, [(0, 1, 2, 3, 4)]), perm_from_cycles(12, [tuple(range(5, 12))])]
        return gens, 12
    if name == 'S5xD7fib':  # {(g,d) in S5 x D7 : sgn g = chi(d)}
        r = lambda i: 5 + ((i + 1) % 7)
        refl = lambda i: 5 + ((-i) % 7)
        g1 = tuple([1, 0, 2, 3, 4] + [5 + ((-i) % 7) for i in range(7)])  # transposition + reflection
        g2 = tuple([1, 2, 0, 3, 4] + list(range(5, 12)))
        g3 = tuple([1, 2, 3, 4, 0] + list(range(5, 12)))
        g4 = tuple(list(range(5)) + [5 + ((i + 1) % 7) for i in range(7)])
        return [g1, g2, g3, g4], 12
    if name == 'A5xZ14':
        gens = [perm_from_cycles(19, [(0, 1, 2)]), perm_from_cycles(19, [(0, 1, 2, 3, 4)]),
                tuple(list(range(5)) + [5 + ((i + 1) % 14) for i in range(14)])]
        return gens, 19
    if name == 'S5xZ7':
        gens = [perm_from_cycles(12, [(0, 1)]), perm_from_cycles(12, [(0, 1, 2, 3, 4)]), tuple(list(range(5)) + [5 + ((i + 1) % 7) for i in range(7)])]
        return gens, 12
    if name == 'S4xD18':
        gS, _ = S4(); gD, _ = dih(18)
        gens = [tuple(list(g) + list(range(4, 22))) for g in gS] + [tuple(list(range(4)) + [4 + x for x in g]) for g in gD]
        return gens, 22
    if name == 'GL23xD9':
        gl = gl23_gens()
        gG = [linear_perm(M, 3, 2) for M in gl]
        gD, _ = dih(9)
        gens = [tuple(list(g) + list(range(9, 18))) for g in gG] + [tuple(list(range(9)) + [9 + x for x in g]) for g in gD]
        return gens, 18
    if name == 'AGL23xZ2':
        gl = gl23_gens()
        gA, _ = affine(3, 2, gl)
        gens = [tuple(list(g) + [9, 10]) for g in gA] + [tuple(list(range(9)) + [10, 9])]
        return gens, 11
    if name == 'A4xD36':
        gA, _ = A4(); gD, _ = dih(36)
        gens = [tuple(list(g) + list(range(4, 40))) for g in gA] + [tuple(list(range(4)) + [4 + x for x in g]) for g in gD]
        return gens, 40
    if name == 'F7sqH18':
        gens, P = affine(7, 2, [[[2, 0], [0, 1]], [[1, 0], [0, 2]], [[0, 1], [1, 0]]])
        return gens, P
    if name == 'F3cubeSD16x2':
        sd = sd16_in_gl23()
        M = lambda X: [[X[0][0], X[0][1], 0], [X[1][0], X[1][1], 0], [0, 0, 1]]
        gens, P = affine(3, 3, [M(sd[0]), M(sd[1]), [[1, 0, 0], [0, 1, 0], [0, 0, 2]]])
        return gens, P
    if name == 'F81mu10':
        # GF(81) = F3[x]/(f), f primitive quartic; zeta = x^8 of order 10
        p = 3
        def pmul(a, b, f):
            r = [0] * 7
            for i in range(4):
                for j in range(4):
                    r[i + j] = (r[i + j] + a[i] * b[j]) % p
            # reduce mod monic f (f given as list of 4 low coeffs of x^4 + ...)
            for d in range(6, 3, -1):
                c = r[d]
                if c:
                    r[d] = 0
                    for i in range(4):
                        r[d - 4 + i] = (r[d - 4 + i] - c * f[i]) % p
            return tuple(r[:4])
        found = None
        for f in itertools.product(range(3), repeat=4):
            if f[0] == 0:
                continue
            x = (0, 1, 0, 0)
            def pw(a, n):
                res = (1, 0, 0, 0)
                for _ in range(n):
                    res = pmul(res, a, f)
                return res
            one = (1, 0, 0, 0)
            if pw(x, 80) == one and pw(x, 40) != one and pw(x, 16) != one:
                found = f; break
        f = found
        pts = all_vecs(4, 3)
        zeta = (1, 0, 0, 0)
        for _ in range(8):
            zeta = pmul(zeta, (0, 1, 0, 0), f)
        gens = [translation([1 if i == j else 0 for i in range(4)], 3, 4) for j in range(4)]
        mz = [0] * 81
        for v in pts:
            w = pmul(v, zeta, f)
            mz[vec_index(v, 3)] = vec_index(w, 3)
        gens.append(tuple(mz))
        return gens, 81

    if name == 'F81D5':
        # GF(81) with generator zeta (order 5 = x^16) and sigma: x -> x^9 (order 2), sigma zeta sigma = zeta^-1
        p = 3
        def pmul(a, b, f):
            r = [0] * 7
            for i in range(4):
                for j in range(4):
                    r[i + j] = (r[i + j] + a[i] * b[j]) % p
            for d in range(6, 3, -1):
                c = r[d]
                if c:
                    r[d] = 0
                    for i in range(4):
                        r[d - 4 + i] = (r[d - 4 + i] - c * f[i]) % p
            return tuple(r[:4])
        def pw(a, n, f):
            res = (1, 0, 0, 0)
            for _ in range(n):
                res = pmul(res, a, f)
            return res
        one = (1, 0, 0, 0); found = None
        for f in itertools.product(range(3), repeat=4):
            if f[0] == 0: continue
            x = (0, 1, 0, 0)
            if pw(x, 80, f) == one and pw(x, 40, f) != one and pw(x, 16, f) != one:
                found = f; break
        f = found
        pts = all_vecs(4, 3)
        zeta = pw((0, 1, 0, 0), 16, f)
        gens = [translation([1 if i == j else 0 for i in range(4)], 3, 4) for j in range(4)]
        mz = [0] * 81
        ms = [0] * 81
        for v in pts:
            mz[vec_index(v, 3)] = vec_index(pmul(v, zeta, f), 3)
            ms[vec_index(v, 3)] = vec_index(pw(v, 9, f), 3)
        gens.append(tuple(mz)); gens.append(tuple(ms))
        return gens, 81
    if name == 'F7sqHa':  # F_7^2 x| (Z3^2 x Z2), Z2 = -I
        gens, P = affine(7, 2, [[[2, 0], [0, 1]], [[1, 0], [0, 2]], [[6, 0], [0, 6]]])
        return gens, P
    if name == 'F7sqHc':  # F_7^2 x| <diag(2,1), swap, -I>
        gens, P = affine(7, 2, [[[2, 0], [0, 1]], [[0, 1], [1, 0]], [[6, 0], [0, 6]]])
        return gens, P
    if name == 'ASL23xV4':  # F_3^2 x| SL(2,3) times Z2 x Z2
        sl = [[[1, 1], [0, 1]], [[0, 1], [2, 0]], [[1, 0], [1, 1]]]
        gA, _ = affine(3, 2, sl)
        gens = [tuple(list(g) + [9, 10, 11, 12]) for g in gA] + [tuple(list(range(9)) + [10, 9, 11, 12]), tuple(list(range(9)) + [9, 10, 12, 11])]
        return gens, 13
    raise SystemExit('unknown ' + name)

if __name__ == '__main__':
    name = sys.argv[1]
    gens, P = build(name)
    N, T = table(gens, P)
    with open(name + '.tab', 'w') as fh:
        fh.write(f'{N}\n')
        for i in range(N):
            fh.write(' '.join(map(str, T[i])) + '\n')
    print(name, 'order', N, 'points', P)
