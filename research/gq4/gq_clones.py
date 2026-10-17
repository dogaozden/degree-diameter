"""Diameter 4, degree q+2: the generalized quadrangle Q(4,q) plus point clones on an ovoid plus line clones on a
partial spread (q odd).

Q(4,q): points of the parabolic quadric x0^2 + x1*x2 + x3*x4 = 0 in PG(4,q), lines = lines of PG(4,q) on it.
(q+1)(q^2+1) points and as many lines, every point on q+1 lines, every line with q+1 points; its incidence graph is
the bipartite Moore graph of degree q+1 and diameter 4.
Ovoid: the section by the hyperplane x4 = lam*x3 with -lam a non-square is an elliptic quadric, q^2+1 points, and
meets every line of Q(4,q) exactly once.
Partial spread: pairwise disjoint lines, found here by randomized greedy plus a swap search.

Clone a point a: a new point on every line through a. Clone a line L: a new line through every point of L.
Point clones on an ovoid add exactly one to every old line; line clones on a partial spread add one to each point
they cover. So the maximum degree is q+2, and (GQ axioms) every distance stays within 4. Order:
2(q+1)(q^2+1) + (q^2+1) + s, where s is the size of the partial spread.

More room: at degree q+1+j, clone every ovoid point j times and every spread line j times (each old line then gains
exactly j, each covered point j). Order 2(q+1)(q^2+1) + j(q^2+1) + j*s.

Usage: python3 gq_clones.py q [seconds_for_spread_search] [j]
Writes the graph to graphs/gq4_q{q}[_j{j}]_n{n}.json when lib.is_valid passes.
"""
import itertools
import json
import random
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'problems' / 'bipartite_dd'))
import lib  # noqa: E402


def normalize(v, F):
    for x in v:
        if x:
            inv = F.inv(x)
            return tuple(F.mul(inv, y) for y in v)
    raise ValueError('zero vector')


def q4(q):
    F = lib.GF(q)
    sq = lambda x: F.mul(x, x)
    Qf = lambda v: F.add(F.add(sq(v[0]), F.mul(v[1], v[2])), F.mul(v[3], v[4]))
    pts = sorted({normalize(v, F) for v in itertools.product(range(q), repeat=5) if any(v) and Qf(v) == 0})
    idx = {p: i for i, p in enumerate(pts)}
    # Polar form of Q: B(u,v) = 2u0v0 + u1v2 + u2v1 + u3v4 + u4v3.
    two = F.add(1, 1)
    B = lambda u, v: F.add(F.add(F.add(F.mul(two, F.mul(u[0], v[0])), F.add(F.mul(u[1], v[2]), F.mul(u[2], v[1]))),
                                 F.mul(u[3], v[4])), F.mul(u[4], v[3]))
    lines = set()
    for i, p in enumerate(pts):
        for j in range(i + 1, len(pts)):
            r = pts[j]
            if B(p, r) == 0:  # p, r on Q and orthogonal: the whole line pr is on Q
                line = {i, j}
                for a in range(1, q):
                    w = normalize(tuple(F.add(p[k], F.mul(a, r[k])) for k in range(5)), F)
                    line.add(idx[w])
                lines.add(frozenset(line))
    lines = sorted(lines, key=sorted)
    assert len(pts) == (q + 1) * (q * q + 1) and len(lines) == len(pts), (len(pts), len(lines))
    assert all(len(L) == q + 1 for L in lines)
    # Ovoid: hyperplane x4 = lam*x3 with -lam a non-square.
    squares = {sq(x) for x in range(1, q)}
    lam = next(l for l in range(1, q) if F.neg(l) not in squares)
    ovoid = [i for i, p in enumerate(pts) if p[4] == F.mul(lam, p[3])]
    assert len(ovoid) == q * q + 1, len(ovoid)
    os_ = set(ovoid)
    assert all(len(L & os_) == 1 for L in lines), 'not an ovoid'
    return pts, lines, ovoid


def partial_spread(lines, seconds, seed=0):
    """A large set of pairwise disjoint lines: randomized greedy, then (1 out, 2 in) swaps."""
    rng = random.Random(seed)
    on = {}
    for j, L in enumerate(lines):
        for p in L:
            on.setdefault(p, []).append(j)
    nbrs = [set() for _ in lines]
    for p, js in on.items():
        for a in js:
            nbrs[a].update(js)
    for a in range(len(lines)):
        nbrs[a].discard(a)
    best = []
    t_end = time.time() + seconds
    while time.time() < t_end:
        order = list(range(len(lines)))
        rng.shuffle(order)
        chosen, blocked = set(), [0] * len(lines)
        for a in order:
            if not blocked[a]:
                chosen.add(a)
                for b in nbrs[a]:
                    blocked[b] += 1
        improved = True
        while improved and time.time() < t_end:  # swap one chosen line for two free ones when possible
            improved = False
            for a in list(chosen):
                chosen.discard(a)
                for b in nbrs[a]:
                    blocked[b] -= 1
                free = [b for b in nbrs[a] | {a} if not blocked[b] and b not in chosen]
                rng.shuffle(free)
                got = []
                for b in free:
                    if not blocked[b]:
                        got.append(b); chosen.add(b)
                        for c in nbrs[b]:
                            blocked[c] += 1
                if len(got) >= 2:
                    improved = True
                    break
                for b in got:  # undo, put a back
                    chosen.discard(b)
                    for c in nbrs[b]:
                        blocked[c] -= 1
                chosen.add(a)
                for b in nbrs[a]:
                    blocked[b] += 1
        if len(chosen) > len(best):
            best = sorted(chosen)
    assert all(not (lines[a] & lines[b]) for a, b in itertools.combinations(best, 2))
    return best


def build(q, seconds=20, j=1):
    pts, lines, ovoid = q4(q)
    spread = partial_spread(lines, seconds)
    P, L = len(pts), len(lines)
    edges = [(p, P + j) for j, Ln in enumerate(lines) for p in Ln]   # points 0..P-1, lines P..P+L-1
    base = P + L
    lines_through = {}
    for k, Ln in enumerate(lines):
        for p in Ln:
            lines_through.setdefault(p, []).append(k)
    clones_p = [a for a in ovoid for _ in range(j)]                   # point clones, j per ovoid point
    clones_l = [b for b in spread for _ in range(j)]                  # line clones, j per spread line
    for i, a in enumerate(clones_p):
        edges += [(base + i, P + k) for k in lines_through[a]]
    for i, b in enumerate(clones_l):
        edges += [(p, base + len(clones_p) + i) for p in lines[b]]
    n = base + len(clones_p) + len(clones_l)
    return n, edges, len(spread)


if __name__ == '__main__':
    q = int(sys.argv[1])
    secs = float(sys.argv[2]) if len(sys.argv) > 2 else 20
    j = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    t0 = time.time()
    n, edges, s = build(q, secs, j)
    ok = lib.is_valid(n, edges, q + 1 + j, 4)
    print(f'q={q} j={j}: GQ part {2*(q+1)*(q*q+1)}, ovoid {q*q+1} x{j}, partial spread {s} x{j}: n={n}, degree {q+1+j}, diameter 4, '
          f'valid={ok} ({time.time()-t0:.0f}s)', flush=True)
    if ok:
        out = Path(__file__).resolve().parent / 'graphs' / f'gq4_q{q}{"_j" + str(j) if j > 1 else ""}_n{n}.json'
        out.parent.mkdir(exist_ok=True)
        out.write_text(json.dumps({'case': f'd{q+1+j}D4', 'value': n, 'output': [n, edges]}))
