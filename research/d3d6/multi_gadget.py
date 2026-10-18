"""k disjoint +2 gadgets in one projective plane, at Delta = q+3 (two spare incidences per vertex).

Each gadget g has its own frame (A, ell, P, X0, X1, Xa, Xc) and applies rules 1-6 of research/plus2/REPORT.md
Sec. 3 to the plane incidences. New vertices per gadget: Q, H0, H1, Ha, Hc (points) and M, K0, K1, Ka, Kc (lines).
python3 multi_gadget.py q k trials [seed]
"""
import json
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / 'research' / 'plus2'))
sys.path.insert(0, str(HERE.parents[1] / 'problems' / 'bipartite_dd'))
import construction as C  # noqa: E402
import lib  # noqa: E402


def gadget_incidences(lines, frames):
    inc = {(('p', p), ('l', j)) for j, L in enumerate(lines) for p in L}
    add = set(); rem = set()
    for g, (A, ell, P, X) in enumerate(frames):
        if len(X) <= 2:
            small_gadget(lines, g, A, ell, P, X, add, rem)
            continue
        if len(X) == 3:
            al_gadget(lines, g, A, ell, P, X, add, rem)
            continue
        X0, X1, Xa, Xc = X
        AX = {x: C.line_through(lines, A, x) for x in lines[ell]}
        S = {'0': X0, '1': X1, 'a': Xa, 'c': Xc}
        for s, x in S.items():
            rem.add((('p', x), ('l', AX[x])))
        for x, y in ((X1, X0), (Xc, X1), (X0, Xc)):
            add.add((('p', x), ('l', AX[y])))
        for s, x in S.items():
            for j, L in enumerate(lines):
                if x in L and j != ell:
                    add.add((('H', g, s), ('l', j)))
            for p in lines[AX[x]]:
                if p != A:
                    add.add((('p', p), ('K', g, s)))
        rot = {X0, X1, Xc}
        for x in lines[ell]:
            if x not in rot:
                add.add((('p', x), ('M', g)))
                add.add((('Q', g), ('l', AX[x])))
        for s in S:
            add.add((('H', g, s), ('M', g)))
            add.add((('Q', g), ('K', g, s)))
        add.add((('p', A), ('K', g, 'a')))
        add.add((('H', g, 'a'), ('l', ell)))
        add.add((('H', g, '0'), ('K', g, 'c')))
        add.add((('H', g, 'c'), ('K', g, '1')))
        add.add((('H', g, '1'), ('K', g, '0')))
    return (inc - rem) | add


def small_gadget(lines, g, A, ell, P, X, add, rem):
    """m = 1 or 2 hats, no removed incidences: H_s (lines through X_s but ell), K_s (AX_s minus A),
    M = ell minus the X_s plus the hats, Q on AX for X not an X_s and on the K_s; m=2: H0~K1, H1~K0; m=1: H0~K0."""
    AX = {x: C.line_through(lines, A, x) for x in lines[ell]}
    S = {str(i): x for i, x in enumerate(X)}
    for s, x in S.items():
        for j, L in enumerate(lines):
            if x in L and j != ell:
                add.add((('H', g, s), ('l', j)))
        for p in lines[AX[x]]:
            if p != A:
                add.add((('p', p), ('K', g, s)))
        add.add((('H', g, s), ('M', g)))
        add.add((('Q', g), ('K', g, s)))
    for x in lines[ell]:
        if x not in X:
            add.add((('p', x), ('M', g)))
            add.add((('Q', g), ('l', AX[x])))
    if len(X) == 2:
        add.add((('H', g, '0'), ('K', g, '1'))); add.add((('H', g, '1'), ('K', g, '0')))
    else:
        add.add((('H', g, '0'), ('K', g, '0')))


def al_gadget(lines, g, A, ell, P, X, add, rem):
    """Araujo-Pardo--Lopez core (3 hats), as construction.core_incidences(hats=3)."""
    X0, X1, Xa = X
    AX = {x: C.line_through(lines, A, x) for x in lines[ell]}
    S = {'0': X0, '1': X1, 'a': Xa}
    rem.add((('p', Xa), ('l', AX[Xa])))
    for s, x in S.items():
        for j, L in enumerate(lines):
            if x in L and j != ell:
                add.add((('H', g, s), ('l', j)))
        for p in lines[AX[x]]:
            if p != A:
                add.add((('p', p), ('K', g, s)))
    for x in lines[ell]:
        if x not in (X0, X1):
            add.add((('p', x), ('M', g)))
            add.add((('Q', g), ('l', AX[x])))
    for s in S:
        add.add((('H', g, s), ('M', g)))
        add.add((('Q', g), ('K', g, s)))
    add.add((('p', A), ('K', g, 'a')))
    add.add((('H', g, 'a'), ('l', ell)))
    add.add((('H', g, '0'), ('K', g, '1')))
    add.add((('H', g, '1'), ('K', g, '0')))


def to_graph(inc):
    pts = sorted({a for a, b in inc}, key=str); lns = sorted({b for a, b in inc}, key=str)
    ids = {v: i for i, v in enumerate(pts + lns)}
    return len(ids), sorted((ids[a], ids[b]) for a, b in inc)


def random_frame(points, lines, rng):
    ell = rng.randrange(len(lines))
    A = rng.choice(sorted(set(points) - lines[ell]))
    on = sorted(lines[ell]); rng.shuffle(on)
    return A, ell, on[0], on[1:5]


def main():
    q, k, trials = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    rng = random.Random(seed)
    points, lines = C.pg_plane(q)
    Delta = q + 3
    stats = {'deg': 0, 'diam': 0}
    for t in range(trials):
        frames = [random_frame(points, lines, rng) for _ in range(k)]
        n, edges = to_graph(gadget_incidences(lines, frames))
        md = lib.max_degree(n, edges)
        if md > Delta:
            stats['deg'] += 1
            continue
        if not lib.is_valid(n, edges, Delta, 3):
            stats['diam'] += 1
            continue
        out = HERE / 'graphs' / f'multi_q{q}_k{k}_d{Delta}_n{n}.json'
        out.write_text(json.dumps({'case': f'd{Delta}D3', 'value': n, 'output': [n, edges]}))
        json.dump([list(map(lambda z: z if not isinstance(z, list) else z, f)) for f in frames],
                  open(HERE / 'runs' / f'multi_q{q}_k{k}_frames.json', 'w'))
        print(f'trial {t}: VALID n={n} maxdeg={md}', out, flush=True)
        return
    print('no valid graph', stats)


if __name__ == '__main__':
    main()
