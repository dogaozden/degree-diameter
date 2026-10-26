# Round 5 cards (12). Read HEADER.md first. Folder: research/squads/b48/r5/<card>/

T = /home/user/degree-diameter/research/squads/b48/tools. Use `$T/lift` for bases with loops, semi-edges or odd cycles
(flift only does bipartite bases without loops). New lift option: `NOTREE=1 ODDSTRIDE=m` draws only voltages with odd
parity for meta:m:k:r groups with k even (index a + m*j, parity j mod 2), which makes every lift bipartite (HEADER).
Semi-edge voltages must be involutions; with ODDSTRIDE they must be odd involutions (in meta m k r: j = k/2 odd, so
k = 2 mod 4, and a (1 + r^(k/2)) = 0 mod m). Group tables from groups.py/abc.py work too: give ODDSTRIDE = |M| when the
table indexes elements as j*|M| + v (abc.py) or a + m*j (groups.py meta).
Screening: 8-10 s lift runs per (base, group), push the best three for 60 s. score48 with `3 10` or `3 9`.

## (3,10): more than 800 vertices, diameter <= 10

**k01: bi-Cayley with semi-edges, one edge.** Base "2 5 / 0 1 / 0 0 s / 0 0 s / 1 1 s / 1 1 s" (each vertex: the edge plus
two semi-edges), n = 2N, N >= 401. Groups with many odd involutions (meta m k r with k = 2 mod 4, dihedral-type products,
AGL(1,p) x Z_2 ...). Screen and push.

**k02: bi-Cayley with semi-edges, two parallel edges.** Base "2 4 / 0 1 / 0 1 / 0 0 s / 1 1 s", n = 2N, N >= 401. Same
group families as k01.

**k03: bi-Cayley with loops.** Base "2 3 / 0 1 / 0 0 / 1 1" (an edge and a loop at each vertex; a loop gives x ~ x*g and
x ~ x*g^-1), n = 2N, N >= 401, odd loop voltages. Metacyclic groups with k even, order 401..460.

**k04: small non-bipartite cubic bases with parity**: K4 (4 vertices, N >= 201), the prism K3 x K2 (6, N >= 134), the
Moebius ladder on 8 vertices (N >= 101), the Petersen graph (10, N >= 81), cubic circulants C_n(1, n/2) and C_n(a, b, n/2)
for n = 10..16. Groups: meta m k r with k even and other groups with a parity homomorphism. Screen many (base, group)
pairs, push the best.

**k05: Petersen graph lifts, (3,10).** The Petersen graph has 10 vertices, girth 5 and diameter 2: a promising base. Groups
of order 81..100 with a parity (k even metacyclic, Z_2 x odd group, dihedral-type, AGL(1,p)-type...), n = 810..1,000.
Screen widely (they are fast), push the best three.

**k06: exhaustive 3+3 certification.** For the best groups of order 134..150 on the 3+3 cubic bases (h04 in round 4: meta 17
8 4 at cost 2 is already proved minimal; others: meta 7 20 6 cost 8, meta 9 16 8 cost 12), run an exhaustive scan of all
voltage assignments (3+3 cubic bases have 4 free voltages: N^4, reduce by simultaneous conjugation as round-4 cards h01..h03
did), using `$T/flift BASE GROUP 3 10 eval` with LIMIT=2 ONLYLOW=1. Report each group's true minimum.

**k07: base graphs with mixed edges, loops and semi-edges on 2..6 vertices** (all cubic), enumerated systematically, with
metacyclic groups of order ceil(802/b)..ceil(900/b) and the parity rule. Screen and push.

## (3,9): more than 506 vertices, diameter <= 9

**k08: bi-Cayley with semi-edges or loops at (3,9)**: the bases of k01, k02 and k03 with N >= 254 (n >= 508).

**k09: non-bipartite cubic bases at (3,9)**: K4 (N >= 127), prism (N >= 85), Moebius ladder 8 (N >= 64), Petersen (N >= 51),
cubic circulants; groups with a parity. Screen and push.

**k10: exhaustive 3+3 at (3,9)**: the 3+3 cubic bases with groups of order 85..100 (n = 510..600): screen with flift, then
exhaust the best two (N^4 assignments, ~5*10^7 at N = 85).

## Wildcards

**k11: cubic wildcard (3,10).** Anything not in k01..k10 or rounds 1-4 (read r4/cards.md). Say which in "idea".
**k12: cubic wildcard (3,9).** Same, for (3,9).
