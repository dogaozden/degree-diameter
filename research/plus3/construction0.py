"""The four-hat graph with NO change to the plane: every incidence of the projective plane is
kept, and the rotation of the +2 rule lives on the copies instead of on the plane.

Projective plane of order q >= 3; line ell, point A not on ell, distinct points Xa, X1, X2, X3
on ell, and the 3-cycle s: 1 -> 2 -> 3 -> 1.  AX is the line through A and X.
New points Q (copy of A), Ha, H1, H2, H3 (copies of the Xs); new lines M (copy of ell),
Ka, K1, K2, K3 (copies of the AXs).  Incidences (plus all of the plane):
  Q  : every line through A except AX1, AX2, AX3;  Ka, K1, K2, K3
  Ha : every line through Xa except AXa;           M, Ka
  Hi : every line through Xi except ell and AXi;   AX_{s(i)};  M, Ki
  M  : every point of ell except X1, X2, X3;       Ha, H1, H2, H3
  Ka : every point of AXa except Xa;               Ha, Q
  Ki : every point of AXi except A and Xi;         X_{s^-1(i)};  Q, Hi
Order 2(q^2+q+6), maximum degree q+2, diameter 3 (checked below).

Usage: python construction0.py [trials]   (random frames per q; saves one graph per q)
"""
import json
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'plus2'))
from construction import pg_plane, line_through, lib  # noqa: E402
import nearfield_plane  # noqa: E402


def build0(points, lines, A, ell, X):
    Xa, X1, X2, X3 = X
    assert A not in lines[ell] and all(x in lines[ell] for x in X) and len(set(X)) == 4
    AX = {x: line_through(lines, A, x) for x in lines[ell]}
    hats = [X1, X2, X3]
    succ = {X1: X2, X2: X3, X3: X1}
    pred = {v: k for k, v in succ.items()}
    inc = {(('p', p), ('l', j)) for j, L in enumerate(lines) for p in L}
    Q, M = ('Q',), ('M',)
    H = {x: ('H', x) for x in X}
    K = {x: ('K', x) for x in X}
    for j, L in enumerate(lines):
        if A in L and j not in {AX[x] for x in hats}:
            inc.add((Q, ('l', j)))
        if Xa in L and j != AX[Xa]:
            inc.add((H[Xa], ('l', j)))
        for x in hats:
            if x in L and j not in (ell, AX[x]):
                inc.add((H[x], ('l', j)))
    for x in hats:
        inc.add((H[x], ('l', AX[succ[x]])))
    for x in X:
        inc.add((Q, K[x]))
        inc.add((H[x], M))
        inc.add((H[x], K[x]))
    for p in lines[ell]:
        if p not in hats:
            inc.add((('p', p), M))
    for p in lines[AX[Xa]]:
        if p != Xa:
            inc.add((('p', p), K[Xa]))
    for x in hats:
        for p in lines[AX[x]]:
            if p not in (A, x):
                inc.add((('p', p), K[x]))
        inc.add((('p', pred[x]), K[x]))
    pts = [('p', p) for p in points] + [Q] + [H[x] for x in X]
    lns = [('l', j) for j in range(len(lines))] + [M] + [K[x] for x in X]
    ids = {v: i for i, v in enumerate(pts + lns)}
    edges = sorted((ids[a], ids[b]) for a, b in inc)
    return len(ids), edges


def plane_kept(points, lines, n_old, edges):
    """True if the old-old edges are exactly the plane's incidences."""
    N = len(points)
    old = {(a, b - (N + 5)) for a, b in edges if a < N and N + 5 <= b < N + 5 + N}
    return old == {(p, j) for j, L in enumerate(lines) for p in L}


def main():
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    for q in (3, 4, 5, 7, 8, 9, 11, 13, 16):
        points, lines = pg_plane(q)
        rng = random.Random(q)
        ok_all = True
        for t in range(trials):
            ell = rng.randrange(len(lines))
            A = rng.choice(sorted(set(points) - lines[ell]))
            X = rng.sample(sorted(lines[ell]), 4)
            n, edges = build0(points, lines, A, ell, X)
            ok = lib.is_valid(n, edges, q + 2, 3) and plane_kept(points, lines, n, edges)
            ok_all &= ok
            if t == 0:
                out = HERE / 'graphs' / f'zero_change_q{q}_d{q+2}_n{n}.json'
                out.write_text(json.dumps({'case': f'd{q+2}D3', 'value': n, 'output': [n, edges]}))
        print(f'q={q}: n={n} = 2(q^2+q+6)={2*(q*q+q+6)}  {trials} random frames, all valid and plane kept: {ok_all}',
              flush=True)
    # a non-Desarguesian plane of order 9 (Hall / nearfield plane), as in plus2/nearfield_plane.py
    points, lines = nearfield_plane.plane(nearfield_plane.nf)
    assert nearfield_plane.is_projective_plane(points, lines)
    rng = random.Random(99)
    ok_all = True
    for t in range(trials):
        ell = rng.randrange(len(lines))
        A = rng.choice(sorted(set(points) - set(lines[ell])))
        X = rng.sample(sorted(lines[ell]), 4)
        n, edges = build0(points, [frozenset(L) for L in lines], A, ell, X)
        ok_all &= lib.is_valid(n, edges, 11, 3)
    print(f'nearfield plane q=9: n={n}, {trials} random frames, all valid: {ok_all}', flush=True)


if __name__ == '__main__':
    main()
