# Round 4 cards (14). Read HEADER.md first. Folder: research/squads/b48/r4/<card>/

T = /home/user/degree-diameter/research/squads/b48/tools. Groups: `meta:m:k:r` strings for flift/lift, or tables from
`python3 $T/groups.py "SPEC" G.bin` / `python3 $T/abc.py build "k p:d,..." G.bin`.
Exhaustive 2+2 cubic scan of one group G of order N: the base $T/bases/cubic/b22_cubic.txt has 6 edges; flift fixes no tree
in eval mode, so feed all 6 voltages with edges 0, 2, 3 at the identity (0) and the other three free:
`python3 -c "N=...; [print(f'0 {a} 0 0 {b} {c}') for a in range(N) for b in range(N) for c in range(N)]" |
 LIMIT=2 ONLYLOW=1 $T/flift $T/bases/cubic/b22_cubic.txt GROUP 3 10 eval` (stderr gives the minimum; cost-0 lines are
solutions: rebuild the edges with (u,x) ~ (v, g*x), left multiplication, or run flift's annealer from them, then score48).
Writing the N^3 lines from Python is the slow part: write them from a small C program or numpy if you can.

## (3,10): more than 800 vertices, diameter <= 10

**h01: exhaustive 2+2 scan, group order 208 (n = 832).** The earlier session finished only 43 of 174 group specs of this
order. Build as many non-abelian groups of order 208 = 16 * 13 as you can (metacyclic m*k = 208 with every r; direct
products such as (Z_13 x| Z_4) x Z_4, D_13 x Z_8, Q8 x D_13...; semidirect Z_13 x| Q for Q of order 16 acting through
Z_4 or Z_2; abc groups) and scan each exhaustively (208^3 = 9.0 million). Report the minimum per group.

**h02: exhaustive 2+2 scan, group orders 209..216 (n = 836..864).** Same as h01 for these orders (skip abelian groups).

**h03: exhaustive 2+2 scan, group orders 217..230.** Same as h01 (orders with few non-abelian groups go fast).

**h04: 3+3 cubic lifts, group order 134..170 (n = 804..1,020).** Bases: $T/bases/cubic/k33.txt and the other connected
cubic bipartite multigraphs on 3+3 vertices (enumerate them: 3x3 matrices with row and column sums 3). Anneal with
flift (D = 10) on metacyclic and abc groups, screen 8 s each, push the best. The earlier session's near miss was 3+3 with
Z_17 x| Z_8 (n = 816) at cost 2.

**h05: 4+4 cubic bases**, group order 101..130 (n = 808..1,040): the cube Q_3, the 8-cycle with alternate doubled edges,
and the other connected cubic bipartite multigraphs on 4+4 vertices. flift annealing, screen and push.

**h06: classic cubic bases**: heawood (14 vertices) x groups of order >= 58 (n >= 812), moebius_kantor (16) x >= 51,
pappus (18) x >= 45, desargues (20) x >= 41, tutte8 (30) x >= 27. Metacyclic/abc/dihedral groups; flift annealing.

**h07: cubic Cayley graphs at (3,10)**: bipartite Cayley graphs with 3 involution generators (base: 1 vertex with 3
semi-edges, "1 3 / 0 0 s / 0 0 s / 0 0 s"; use lift, which supports semi-edges and checks bipartiteness) or with
{a, a^-1, t} ("1 2 / 0 0 / 0 0 s"), groups of order 802..900 with an index-2 subgroup: e.g. AGL(1,29) (812),
meta groups with even k, PGL(2,q)-type, dihedral-type products.

## (3,9): more than 506 vertices, diameter <= 9

**h08: exhaustive 2+2 scan at (3,9)**, group orders 127..140 (n = 508..560), D = 9 (same recipe as h01; prime orders
have only cyclic groups, skip them; order 128 has too many groups, take metacyclic and abc ones).

**h09: 3+3 and 4+4 cubic lifts at (3,9)**: 3+3 with groups of order 85..100 (n = 510..600), 4+4 with order 64..80.
flift annealing, screen, push, and exhaust the best 3+3 group if the space allows (N^4 assignments).

**h10: classic cubic bases at (3,9)**: heawood x order >= 37 (n >= 518), moebius_kantor x >= 32, pappus x >= 29,
desargues x >= 26, tutte8 x >= 17 (n >= 510), and gh2 (126 vertices, the generalized hexagon GH(2,2) incidence graph,
girth 12) x groups of order >= 5 (n >= 630) with lift (flift allows at most 64 base vertices).

## Wildcards

**h12: cubic wildcard.** Any direction for (3,9) or (3,10) not in h01..h10. Say which cell and idea.

## (4,9) follow-ups

**h13: (4,9) without a central involution.** Card d16 found that in meta 104 24 7 (m even, r odd) the central involution
(52, 0) is far in every cost-4 solution. Screen groups of order 2,496..2,700 with no central involution (m odd, or r
acting without fixed points on the 2-part) and many classes; compare with d16's suggestion of forcing z with a pair
(s, s z) in S. haar_fast/haar_tab with D = 9.

**h14: (4,9) 2+2 and 3+3 lifts with large non-abelian groups at D = 9** beyond round 3 (d10 reached cost 24 on 2+2 with
Z_251 x| Z_5): try groups with large k (Z_m x| Z_k, k >= 12) of order 1,243..1,400 on 2+2, and order 829..930 on 3+3.
