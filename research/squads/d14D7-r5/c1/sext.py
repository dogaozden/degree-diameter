#!/usr/bin/env python3
"""c1: the principal PGL(2,11) acting on binary sextics (Sym^6 of the natural module), and its subgroups.

A 2x2 matrix A = [[a,b],[c,d]] acts on f(x,y) by f -> f o A, (x,y) -> (a x + b y, c x + d y).  In the monomial basis
e_i = x^(6-i) y^i (i = 0..6) this gives a 7x7 matrix M(A) (column i = coefficients of (ax+by)^(6-i) (cx+dy)^i).
The map is an anti-homomorphism, which does not matter for the generated group.  Scalars act as scalars, so the
image of GL(2,11) in PGL(7,11) is PGL(2,11) (order 1320).  An SL2-invariant symmetric form S on the sextics is found
with ovlib.invariant_forms; GL2 elements multiply S by a scalar (det^6), so the groups are conjugated with
ovlib.conjugate_to_standard, which allows a multiple.

Subgroups of PGL(2,11) are enumerated as 2-generated subgroups of the projective group; one generating pair is kept
per (order, element-order signature) class.  Output: gens files for orbclq.
"""
import sys, os, random, itertools, json
OV = '/home/user/degree-diameter/research/cell147/ovoid'
sys.path.insert(0, OV)
import ovlib

q = 11
HERE = os.path.dirname(os.path.abspath(__file__))


def conv(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] = (r[i + j] + x * y) % q
    return r


def sextic(A):
    """7x7 matrix of f -> f o A on coefficient vectors (coefficient j = coefficient of x^(6-j) y^j)."""
    (a, b), (c, d) = A
    lin1, lin2 = [a % q, b % q], [c % q, d % q]
    M = [[0] * 7 for _ in range(7)]
    for i in range(7):
        L = [1]
        for _ in range(6 - i): L = conv(L, lin1)
        for _ in range(i): L = conv(L, lin2)
        for j in range(7): M[j][i] = L[j]
    return M


def mat2_mul(A, B):
    return ((A[0][0] * B[0][0] + A[0][1] * B[1][0]) % q, (A[0][0] * B[0][1] + A[0][1] * B[1][1]) % q), \
           ((A[1][0] * B[0][0] + A[1][1] * B[1][0]) % q, (A[1][0] * B[0][1] + A[1][1] * B[1][1]) % q)


def proj2(A):
    """projective normal form of an invertible 2x2 matrix (first nonzero entry = 1)."""
    flat = [A[0][0], A[0][1], A[1][0], A[1][1]]
    f = next(x for x in flat if x % q)
    s = pow(f, q - 2, q)
    a, b, c, d = [x * s % q for x in flat]
    return ((a, b), (c, d))


def det2(A): return (A[0][0] * A[1][1] - A[0][1] * A[1][0]) % q


def pgl_elements():
    els = set()
    for a, b, c, d in itertools.product(range(q), repeat=4):
        if (a * d - b * c) % q:
            els.add(proj2(((a, b), (c, d))))
    return sorted(els)


def closure(gens):
    I = proj2(((1, 0), (0, 1)))
    G = {I}; frontier = [I]
    while frontier:
        nf = []
        for X in frontier:
            for g in gens:
                Y = proj2(mat2_mul(X, g))
                if Y not in G:
                    G.add(Y); nf.append(Y)
        frontier = nf
    return G


def proj_order(A):
    I = proj2(((1, 0), (0, 1)))
    X, k = proj2(A), 1
    while X != I:
        X = proj2(mat2_mul(X, A)); k += 1
    return k


# ---- the invariant form and the standard-coordinate groups ----
U = ((1, 1), (0, 1))
W = ((0, 1), (10, 0))            # [[0,1],[-1,0]]
T = ((2, 0), (0, 6))             # diag(2, 2^-1): 2 is a primitive root mod 11
DIAG2 = ((2, 0), (0, 1))         # det 2 (non-square): GL2 element
LOW = ((1, 0), (1, 1))


def invariant_S():
    forms = ovlib.invariant_forms([sextic(U), sextic(W), sextic(T)], q)
    assert len(forms) == 1, len(forms)
    S = forms[0]
    assert ovlib._rank(S, q) == 7
    return S


S_FORM = invariant_S()
G_STD = ovlib.std_gram(q)


def std_mats(A_list):
    """standard-coordinate 7x7 matrices of the given 2x2 generators (similitudes of the standard form)."""
    mats = [sextic(A) for A in A_list]
    mats2, P = ovlib.conjugate_to_standard(mats, S_FORM, q)
    for M in mats2:
        Mt = ovlib.mat_mul(ovlib.mat_mul(ovlib.mat_T(M), G_STD, q), M, q)
        mu = next(Mt[i][j] * pow(G_STD[i][j], q - 2, q) % q for i in range(7) for j in range(7) if G_STD[i][j])
        assert Mt == [[x * mu % q for x in r] for r in G_STD], 'not a similitude of the standard form'
    return mats2


def write_std(path, A_list, comment):
    ovlib.write_gens(path, std_mats(A_list), comment)



def closure_capped(gens, cap):
    I = proj2(((1, 0), (0, 1)))
    G = {I}; frontier = [I]
    while frontier:
        nf = []
        for X in frontier:
            for g in gens:
                Y = proj2(mat2_mul(X, g))
                if Y not in G:
                    G.add(Y); nf.append(Y)
                    if len(G) > cap: return None
        frontier = nf
    return G


def enumerate_classes(cap=130):
    """conjugacy-class-like representatives of subgroups of PGL(2,11): cyclic groups <x>, groups <x,y> with y an
    involution and |<x,y>| <= cap, and the explicit Borel / PSL / PGL groups.  Returns {(order, sig): gens}."""
    from collections import Counter
    E = pgl_elements()
    invols = [x for x in E if proj_order(x) == 2]
    cyc = {}
    for x in E:
        key = frozenset(closure([x]))
        cyc.setdefault(key, x)
    classes = {}
    def add(gens, H):
        sig = tuple(sorted(Counter(proj_order(h) for h in H).items()))
        cls = (len(H), sig)
        if cls not in classes: classes[cls] = gens
    for key, x in cyc.items(): add([x], key)
    for x in cyc.values():
        for y in invols:
            H = closure_capped([x, y], cap)
            if H is not None: add([x, y], H)
    # explicit big groups
    U = ((1, 1), (0, 1)); D2 = ((2, 0), (0, 1)); Wn = ((0, 1), (1, 0)); L = ((1, 0), (1, 1)); W0 = ((0, 1), (10, 0))
    for gens in ([U, D2], [U, ((4, 0), (0, 1))], [D2, Wn], [U, L], [U, W0], [U, L, D2]):
        H = closure(gens); add(gens, H)
    return classes


if __name__ == '__main__':
    import time
    t0 = time.time()
    cl = enumerate_classes()
    print('classes', len(cl), 'time %.1f' % (time.time() - t0))
    for cls in sorted(cl, key=lambda c: (c[0], c[1])):
        print(cls[0], cls[1], cl[cls])
