"""Several self-polar four-hat gadgets on one plane at Delta = q+3 (target (16,3), q = 13; lab value 396).

A self-polar gadget is given by its frame point set F = {A, Z, Z', X, X^tau}: A external to the conic, Z, Z' the
points of contact of the tangents from A, {X, X^tau} a conjugate pair on ell = A^perp.  On an intact plane the
gadget raises by one the degree of exactly the points p whose polar line meets F (and, dually, of the lines meeting
F).  So k gadgets fit at Delta = q+3 if no line meets three of the frames (degree condition; checked afterwards on
the built structure).  Step 1: search k-sets of frames with no line meeting three of them.  Step 2: build the
structure for each labelling and check degrees and diameter 3.
Usage: python gadgets16.py q k [max_solutions]
"""
import itertools
import sys
import time

from pg2 import PG2, hats, split, diameter3

q = int(sys.argv[1]) if len(sys.argv) > 1 else 13
k = int(sys.argv[2]) if len(sys.argv) > 2 else 4
maxsol = int(sys.argv[3]) if len(sys.argv) > 3 else 50
Pi = PG2(q)
C = Pi.conic()
lidx = {L: i for i, L in enumerate(Pi.lines)}
ext = [p for p in Pi.points if p not in C and len(Pi.pts_on[Pi.perp(p)] & C) == 2]
frames = []
for A in ext:
    ell = Pi.perp(A)
    Z, Z2 = sorted(Pi.pts_on[ell] & C)
    seen = set()
    for X in sorted(Pi.pts_on[ell] - C):
        Xt = Pi.meet(Pi.perp(X), ell)
        key = frozenset((X, Xt))
        if key in seen:
            continue
        seen.add(key)
        F = (A, Z, Z2, X, Xt)
        mask = 0
        for x in F:
            for L in Pi.lines_on[x]:
                mask |= 1 << lidx[L]
        frames.append((F, mask))
print(f'q={q}: {len(ext)} external points, {len(frames)} frames; each frame meets '
      f'{bin(frames[0][1]).count("1")} lines', flush=True)

# conic group orbit representatives for the first frame: frames with A = (0,1,0) suffice (the conic group is
# transitive on external points); then every pair at A is tried as the first frame.
A0 = Pi.pt((0, 1, 0))
first = [i for i, (F, m) in enumerate(frames) if F[0] == A0]


def search():
    t0 = time.time()
    sols = []
    n = len(frames)

    def rec(chosen, once, twice):
        if len(chosen) == k:
            sols.append(list(chosen))
            return len(sols) >= maxsol
        start = chosen[-1] + 1 if len(chosen) > 1 else 0
        for j in range(start, n):
            if j in chosen:
                continue
            m = frames[j][1]
            if m & twice:
                continue
            if any(set(frames[j][0]) & set(frames[c][0]) for c in chosen):
                continue          # frames must be disjoint (in particular distinct A)
            if rec(chosen + [j], once | m, twice | (once & m)):
                return True
        return False
    for i in first:
        if rec([i], frames[i][1], 0):
            break
    print(f'  {len(sols)} degree-compatible {k}-sets found (stopped at {maxsol}) in {time.time() - t0:.1f}s', flush=True)
    return sols


def build(sol, labels):
    inc = set(Pi.inc)
    news = set()
    for g, (j, (swapZ, swapX)) in enumerate(zip(sol, labels)):
        A, Z, Z2, X, Xt = frames[j][0]
        if swapZ:
            Z, Z2 = Z2, Z
        if swapX:
            X, Xt = Xt, X
        ell = Pi.perp(A)
        sub = hats(Pi, A, ell, {'a': Z, 'c': Z2, 0: X, 1: Xt}, '4')
        old_removed = Pi.inc - sub
        inc -= old_removed
        for p, L in sub - Pi.inc:
            tag = lambda x: (x[0], g) + tuple(x[1:]) if x[0] in ('Q', 'M', 'H', 'K') else x
            inc.add((tag(p), tag(L)))
    return inc


sols = search()
for sol in sols:
    for labels in itertools.product(itertools.product((0, 1), repeat=2), repeat=k):
        inc = build(sol, labels)
        pts, lns, lo, po = split(inc)
        md = max(max(len(v) for v in lo.values()), max(len(v) for v in po.values()))
        if md > q + 3:
            print(f'  frames {sol} labels {labels}: maxdeg {md} > q+3', flush=True)
            continue
        d3 = diameter3(inc)
        print(f'  frames {sol} labels {labels}: elements {len(pts) + len(lns)}, maxdeg {md}, diameter3 {d3}', flush=True)
        if d3:
            import json
            json.dump(sorted([[repr(p), repr(L)] for p, L in inc]), open(f'gadgets_q{q}_k{k}.json', 'w'))
            print('  FOUND; saved', flush=True)
            sys.exit(0)
        break
print('no valid structure among the degree-compatible sets tried')
