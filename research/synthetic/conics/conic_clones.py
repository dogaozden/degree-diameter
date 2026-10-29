"""Delorme's conic clones at Delta = q+3 (CONICS.md, Section 1.6): PG(2,q), q odd, plus a clone of every point of the
conic and a clone of every tangent line, plus the flags (clone of p, clone of the tangent at p).
Checks: diameter 3, maximum degree q+3, 2(q^2+2q+2) elements, every line contains a point of degree q+3 (so no hat
gadget fits on top), self-polar (clone of p <-> clone of the tangent at p), fold of diameter 2."""
from pg2 import PG2, split, diameter3
from selfpolar import polarity_graph, diameter

for q in (3, 5, 7, 9, 11, 13):
    Pi = PG2(q)
    C = Pi.conic()
    inc = set(Pi.inc)
    for p in C:
        t = Pi.perp(p)
        for L in Pi.lines_on[p]:
            inc.add((('c', p), L))
        for r in Pi.pts_on[t]:
            inc.add((r, ('t', t)))
        inc.add((('c', p), ('t', t)))
    pts, lns, lo, po = split(inc)
    dp = {p: len(lo[p]) for p in pts}
    dl = {L: len(po[L]) for L in lns}
    full_on_every_line = all(any(dp[p] == q + 3 for p in Pi.pts_on[L]) for L in Pi.lines)

    def th(x):
        if x[0] in ('p', 'L'):
            return Pi.perp(x)
        if x[0] == 'c':
            return ('t', Pi.perp(x[1]))
        return ('c', Pi.perp(x[1]))
    pol = all((th(L), th(p)) in inc for p, L in inc)
    _, adj, _ = polarity_graph(inc, th)
    print(f'q={q:2d}: elements={len(pts) + len(lns)} (2(q^2+2q+2)={2 * (q * q + 2 * q + 2)}) maxdeg={max(max(dp.values()), max(dl.values()))} '
          f'diameter3={diameter3(inc)} every line has a full point={full_on_every_line} self-polar={pol} '
          f'fold n={len(adj)} diam={diameter(adj)}')
