"""Map the Singer-orbit 2-ovoid of W(3,q) to an exact 2-cover of Q(4,q) in the indexing of gq_clones.q4(q).

Duality W(3,q) -> Q(4,q) (Klein correspondence): change to a symplectic basis, so B(u,v) = u0v1 - u1v0 + u2v3 - u3v2.
A totally isotropic line <u,v> has Plucker coordinates p_ij = u_i v_j - u_j v_i with p01 + p23 = 0, and the Klein
relation p01 p23 - p02 p13 + p03 p12 = 0 becomes p01^2 + p02 p13 - p03 p12 = 0. So x = (p01, p02, p13, p03, -p12)
lies on gq_clones' quadric x0^2 + x1 x2 + x3 x4 = 0. A point of W(3,q) goes to the line of Q(4,q) formed by the
images of the q+1 totally isotropic lines through it.

The 2-ovoid: points g^i of PG(3,q) = GF(q^4)*/GF(q)* with i mod (q+1) in {a, q-a} (see w3_singer.py). Every
totally isotropic line meets it in exactly 2 points, so every point of Q(4,q) is on exactly 2 of the image lines.

Usage: python3 to_q4.py q [a]   writes research/gq4y/spreads/cover2_q{q}_t{2(q^2+1)}.json (default a = 0)
"""
import json
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'gq4'))
sys.path.insert(0, str(HERE))
from gq_clones import q4  # noqa: E402
from w3_singer import w3, normalize, intersection_profile  # noqa: E402


def symplectic_basis(M, p):
    """Rows e0, f0, e1, f1 (old coordinates) with B(e0,f0) = B(e1,f1) = 1 and all other pairs 0."""
    B = lambda u, v: int(np.array(u) @ M @ np.array(v)) % p
    std = [np.array(r) for r in np.eye(4, dtype=np.int64)]
    basis, rest = [], std
    while rest:
        e = rest[0]
        f = next(w for w in rest[1:] if B(e, w))
        f = (f * pow(B(e, f), p - 2, p)) % p
        basis += [e, f]
        # project the others onto <e,f>-perp: w - B(w,f) e + B(w,e) f
        rest = [(w - B(w, f) * e + B(w, e) * f) % p for w in rest[1:] if w is not f]
        rest = [w for w in rest if w.any()]
        # keep a basis of the complement: drop dependent vectors
        kept = []
        for w in rest:
            if rank(np.array(kept + [w]), p) == len(kept) + 1:
                kept.append(w)
        rest = kept
    P = np.array(basis) % p
    J = np.array([[0, 1, 0, 0], [-1, 0, 0, 0], [0, 0, 0, 1], [0, 0, -1, 0]])
    assert ((P @ M @ P.T - J) % p == 0).all()
    return P


def rank(A, p):
    A = [list(map(int, r)) for r in A]
    r = 0
    for c in range(len(A[0])):
        piv = next((i for i in range(r, len(A)) if A[i][c] % p), None)
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c], p - 2, p)
        A[r] = [x * inv % p for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] % p:
                f = A[i][c]
                A[i] = [(x - f * y) % p for x, y in zip(A[i], A[r])]
        r += 1
    return r


def inverse(A, p):
    n = len(A)
    Aug = [list(map(int, A[i])) + [int(i == j) for j in range(n)] for i in range(n)]
    for c in range(n):
        piv = next(i for i in range(c, n) if Aug[i][c] % p)
        Aug[c], Aug[piv] = Aug[piv], Aug[c]
        inv = pow(Aug[c][c], p - 2, p)
        Aug[c] = [x * inv % p for x in Aug[c]]
        for i in range(n):
            if i != c and Aug[i][c] % p:
                f = Aug[i][c]
                Aug[i] = [(x - f * y) % p for x, y in zip(Aug[i], Aug[c])]
    return np.array([r[n:] for r in Aug], dtype=np.int64)


def main(q, a=0):
    F, X, M, wlines = w3(q)
    N = len(X)
    S = [i for i in range(N) if i % (q + 1) in (a, q - a)]
    assert len(S) == 2 * (q * q + 1) and set(intersection_profile(S, wlines)) == {2}, 'not a 2-ovoid of W(3,q)'

    P = symplectic_basis(M, q)
    C = (X @ inverse(P, q)) % q          # coordinates in the symplectic basis
    pts, lines, ovoid = q4(q)
    pidx = {p: i for i, p in enumerate(pts)}
    lidx = {L: k for k, L in enumerate(lines)}

    # each totally isotropic line of W -> a point of Q(4,q)
    wl2pt = []
    for L in wlines:
        u, v = (C[i] for i in sorted(L)[:2])
        pl = lambda i, j: int(u[i] * v[j] - u[j] * v[i])
        assert (pl(0, 1) + pl(2, 3)) % q == 0
        x = normalize((pl(0, 1), pl(0, 2), pl(1, 3), pl(0, 3), -pl(1, 2)), q)
        wl2pt.append(pidx[x])                            # KeyError if x were off the quadric
    assert len(set(wl2pt)) == len(pts)                   # bijection on points

    # each point of W -> a line of Q(4,q)
    through = {}
    for k, L in enumerate(wlines):
        for i in L:
            through.setdefault(i, []).append(k)
    wp2line = [lidx[frozenset(wl2pt[k] for k in through[i])] for i in range(N)]   # KeyError if not a line
    assert len(set(wp2line)) == len(lines)               # bijection on lines; incidence preserved by construction

    cover = sorted(wp2line[i] for i in S)
    load = [0] * len(pts)
    for k in cover:
        for p in lines[k]:
            load[p] += 1
    assert set(load) == {2}, 'not an exact 2-cover'
    out = HERE / 'spreads' / f'cover2_q{q}_t{len(cover)}.json'
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(cover))
    print(f'q={q} a={a}: {len(cover)} lines, every one of {len(pts)} points on exactly 2 -> {out}')


if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]) if len(sys.argv) > 2 else 0)
