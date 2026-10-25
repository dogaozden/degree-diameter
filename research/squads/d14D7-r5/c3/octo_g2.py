#!/usr/bin/env python3
"""c3: G2 frames from the octonions.  Octonions by Cayley-Dickson (mu=-1), integer vectors.  Coxeter integral units
S (240 = 16 + 14*16 half-units) with doubled integer coordinates.  Frames = 7-tuples of imaginary units of S with the
same product table as e_1..e_7 (f_i f_j = s e_k) -> algebra automorphisms -> 7x7 matrices (columns f_i), reduced mod 11.
Also the signed frames {+-e_i} (2^3.L3(2)).  Writes generator files conjugated to the standard form of Q(6,11)."""
import sys, os, random, itertools, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/cell147/ovoid')
import ovlib

HERE = os.path.dirname(os.path.abspath(__file__))
Q = 11

def qmul(p, q):
    w1, x1, y1, z1 = p; w2, x2, y2, z2 = q
    return (w1*w2 - x1*x2 - y1*y2 - z1*z2,
            w1*x2 + x1*w2 + y1*z2 - z1*y2,
            w1*y2 - x1*z2 + y1*w2 + z1*x2,
            w1*z2 + x1*y2 - y1*x2 + z1*w2)

def qconj(p): return (p[0], -p[1], -p[2], -p[3])

def omul(X, Y):
    """Cayley-Dickson product (a,b)(c,d) = (ac - d* b, d a + b c*)."""
    a, b, c, d = X[:4], X[4:], Y[:4], Y[4:]
    t1 = qmul(a, c); t2 = qmul(qconj(d), b)
    u1 = qmul(d, a); u2 = qmul(b, qconj(c))
    return tuple(t1[i] - t2[i] for i in range(4)) + tuple(u1[i] + u2[i] for i in range(4))

def basis(i):
    v = [0] * 8; v[i] = 1; return tuple(v)

# ---- sanity: norm multiplicativity of the Cayley-Dickson product ----
rng = random.Random(1)
for _ in range(200):
    X = tuple(rng.randint(-3, 3) for _ in range(8)); Y = tuple(rng.randint(-3, 3) for _ in range(8))
    N = lambda Z: sum(t * t for t in Z)
    assert N(omul(X, Y)) == N(X) * N(Y), 'not a normed algebra'

# ---- structure table on e_1..e_7 (index 0 = 1): e_i e_j = s e_k ----
tab = {}
for i in range(1, 8):
    for j in range(1, 8):
        if i == j: continue
        P = omul(basis(i), basis(j))
        ks = [t for t in range(8) if P[t] != 0]
        assert len(ks) == 1 and ks[0] >= 1
        tab[(i, j)] = (ks[0], P[ks[0]])
lines = sorted({tuple(sorted((i, j, tab[(i, j)][0]))) for i in range(1, 8) for j in range(1, 8) if i != j})
assert len(lines) == 7

# ---- Coxeter integral units, doubled coordinates (value 2x) ----
quads = []
for L in lines:
    quads.append((0,) + L)                                  # (+-1 +-e_a +-e_b +-e_c)/2
    quads.append(tuple(sorted(set(range(1, 8)) - set(L))))   # (+-e_p +-e_q +-e_r +-e_s)/2
S = set()
for qd in quads:
    for signs in itertools.product([1, -1], repeat=4):
        v = [0] * 8
        for idx, s in zip(qd, signs): v[idx] = s
        S.add(tuple(v))
for i in range(8):
    for s in (1, -1):
        v = [0] * 8; v[i] = 2 * s; S.add(tuple(v))
assert len(S) == 240, len(S)

def mul2(X, Y):
    P = omul(X, Y)
    assert all(p % 2 == 0 for p in P)
    return tuple(p // 2 for p in P)

closed = all(mul2(X, Y) in S for X in S for Y in S)
print('Coxeter units:', len(S), 'closed under product:', closed, file=sys.stderr)
assert closed

U_imag = sorted(X for X in S if X[0] == 0)
U_signed = sorted(tuple(2 * s if t == i else 0 for t in range(8)) for i in range(1, 8) for s in (1, -1))
print('imaginary units in S:', len(U_imag), ' signed units:', len(U_signed), file=sys.stderr)

def dot4(X, Y): return sum(a * b for a, b in zip(X, Y))

def frames(C):
    """all 7-tuples (F_1..F_7) in C with F_i F_j = s_ij F_k for every i != j (structure table)."""
    out = []
    Cset = set(C)
    for F1 in C:
        for F2 in C:
            if dot4(F1, F2) != 0: continue
            k, s = tab[(1, 2)]
            F3 = tuple(s * x for x in mul2(F1, F2))
            if F3 not in Cset: continue
            for F4 in C:
                if dot4(F4, F1) or dot4(F4, F2) or dot4(F4, F3): continue
                F = {1: F1, 2: F2, 3: F3, 4: F4}
                ok = True
                for m in (5, 6, 7):
                    pair = next((i, j) for i in range(1, 5) for j in range(1, 5) if i != j and tab[(i, j)][0] == m)
                    i, j = pair; s = tab[pair][1]
                    Fm = tuple(s * x for x in mul2(F[i], F[j]))
                    if Fm not in Cset: ok = False; break
                    F[m] = Fm
                if not ok: continue
                # full check of the product table
                for i in range(1, 8):
                    for j in range(1, 8):
                        if i == j: continue
                        k, s = tab[(i, j)]
                        if mul2(F[i], F[j]) != tuple(s * x for x in F[k]): ok = False; break
                    if not ok: break
                if ok:
                    out.append(tuple(F[i] for i in range(1, 8)))
    return out

def to_mod(F):
    """columns F_i (doubled imaginary coords) -> 7x7 matrix over F_11 (entries x = D/2)."""
    return [[(F[c][r + 1] * 6) % Q for c in range(7)] for r in range(7)]

def closure(gens, cap=20000):
    I = np.eye(7, dtype=np.int64)
    seen = {I.tobytes(): I}; frontier = [I]
    G = [np.array(g, dtype=np.int64) for g in gens]
    while frontier:
        nf = []
        for X in frontier:
            for g in G:
                Y = (X @ g) % Q
                k = Y.tobytes()
                if k not in seen:
                    seen[k] = Y; nf.append(Y)
                    if len(seen) > cap: return None
        frontier = nf
    return seen

if __name__ == '__main__':
    t0 = time.time()
    fr_G2 = frames(U_imag)
    print('frames in the 126 Coxeter imaginary units:', len(fr_G2), f'{time.time()-t0:.1f}s', file=sys.stderr)
    fr_23 = frames(U_signed)
    print('signed frames (2^3.L3(2) candidates):', len(fr_23), file=sys.stderr)
    mats_G2 = [to_mod(F) for F in fr_G2]
    mats_23 = [to_mod(F) for F in fr_23]
    # group sizes by closure from random generators
    rng = random.Random(7)
    for name, mats, want in (('G2(2)', mats_G2, len(mats_G2)), ('2^3.L3(2)', mats_23, len(mats_23))):
        for trial in range(20):
            gens = [rng.choice(mats) for _ in range(2)]
            H = closure(gens)
            if H is not None and len(H) == want:
                break
        print(name, 'frames', want, 'closure of 2 random frames has', len(H) if H else None, 'elements', file=sys.stderr)
        if name == 'G2(2)':
            G2_elems = list(H.values()) if H is not None and len(H) == want else None
        else:
            S23_elems = list(H.values()) if H is not None and len(H) == want else None
    import pickle
    pickle.dump({'G2': [m for m in mats_G2], 'S23': [m for m in mats_23]}, open(os.path.join(HERE, 'frames_mod11.pkl'), 'wb'))
    print('saved', os.path.join(HERE, 'frames_mod11.pkl'), file=sys.stderr)
