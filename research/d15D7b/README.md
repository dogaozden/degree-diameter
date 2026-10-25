# (15,7) from typed hexagon levels, mirrored surgery and relaxed friendly sets (job cell-15-7, 2026-10-25)

Best: **(15,7) ≥ 2,501,124** (table 2,480,184; master 2,497,075 at the start of the session),
research/frontier/sols/d15D7_hex11_typedrelax_n2501124.sol, check checks/d15D7_hex11_typedrelax_n2501124.check.txt.

## The graph

Seven levels j = 0..6, each a copy of the incidence graph I of the split Cayley hexagon H(11) (177,156 points, 177,156
lines), with types HHDHHDD (research/squads/cells/d16D7.md). Matchings j -> j+k (k = 1, 2, 3) from the A-class of level j
(points in H levels, lines in H^D levels) to the B-class of level j+k:
- friendly transitions (types differ, 12 of 21): the identity; a freed set (points if j is H, lines if j is H^D);
- non-friendly transitions (9): the mirrored bijection sigma (H -> H) or sigma^-1 (H^D -> H^D) with the 768-element
  mirrored set of research/theorems/MIRRORED_SURGERY.md freed.
Every deleted matching edge leaves a free A-slot (source level) and a free B-slot (target level). Line-side hubs take one
free A-slot in every level, point-side hubs one free B-slot in every level; a hub graph of degree <= 8 joins them.
n = 14·177,156 + KB + KA, KB = min over levels of free A-slots, KA = min of free B-slots.

With levels HHDHHDD the minima sit at levels 0, 1 (A: one friendly transition, 0->2 / 1->2, plus two mirrored ones) and
levels 3, 4 (B: 2->3 / 2->4 plus two mirrored), so KB = min(|P0|, |P1|) + 1,536 and KA = min(|S3|, |S4|) + 1,536 with
P0, P1 the points freed at 0->2, 1->2 and S3, S4 the lines freed at 2->3, 2->4 (the "bottleneck sets"). Any layout with
seven levels and three matchings per class has the same bound (README of research/squads/cells/d15D7.md, step 2).

## Steps and results (all on branch claude/cell-15-7-haar-search-x6ynhl)

| n | what changed | check |
|---|---|---|
| 2,499,748 | cell-14-7 candidate: typed levels + mirrored surgery, equal hub sides 9,782 | builder + hub BFS (other session) |
| 2,500,147 | unequal hub sides 10,181 / 9,782 (hub pairs also meet through the levels) | hub BFS |
| 2,500,749 | relaxed bottleneck sets (collinear / concurrent pairs, RELAXED.md), 2,863 pairs | BFS from hubs + paired vertices |
| 2,501,008 | partner covers designed into the non-bottleneck friendly sets, 3,898 pairs | same |
| **2,501,124** | squad round c157b-r2: private covers (design3.py), protected alternation, refill; 4,370 pairs | same + full apsp_mt (see check file) |

## Files

- RELAXED.md: the relaxed one-transition surgery theorem (pairs in a friendly freed set) with proof.
- tm2_build.py: builder for the unrelaxed construction with unequal hub sides (2,500,147).
- tm3_build.py: general builder: per-transition freed sets with pairs, hub slot table (assign: one bipartite matching per
  level for the pair conditions, two demands may share one hub), (R1)/(R2)/mirror hypotheses re-checked in build, which
  also writes the BFS source list (all hubs and both vertices of every paired element).
- dpack.c: ILS for 1-defective sets (every element at most one partner) with a coverage mask and a protect list.
- pack.c: ILS for plain non-collinear / non-concurrent sets (no gain over 8,645 / 8,246).
- design_cover.py, design3.py (squad c157b-r2 c4): non-bottleneck friendly sets that cover every paired element's partner
  with a private covering element.
- score_relaxed.py: exact scorer (four bottleneck sets -> covers -> assignment -> drops -> n); v3_drop.py; paired.py;
  mkmasks.py, mkmasks2.py (coverage masks).
- hubgen.py, hubfix.py, v3_hub.sh: hub graph (random, unequal sides) and aimed 2-switches until the BFS finds no far pair.
- hubfar.c: bit-parallel BFS from a source list to depth D, prints every pair beyond D.
- dumpsets.py: master's R_H / R_L and the mirrored set as plain id lists.

## Rebuild and check

```
cc -O2 -o hexgen2 research/d13D7/hexgen2.c -lm && mkdir -p hex && ./hexgen2 11        # hex/hex_q11.bin, sha256 e60db369...
python3 research/d15D7b/tm3_build.py build hex/hex_q11.bin research/frontier/sols/d15D7_hex11_typedrelax_n2501124.sol g.edges g.src
cc -O2 -pthread -o hubfar research/d15D7b/hubfar.c && ./hubfar g.edges 7 4 g.src             # hubs + paired vertices
cc -O2 -pthread -o apsp_mt research/lifts/coordinator_check/apsp_mt.c && ./apsp_mt g.edges 15 7 4   # all pairs
```
The .sol lists all twelve friendly sets, the hub slot table and the hub graph, and names the mirror solution
d14D7_hex11_mirror768_n1774632.sol (same folder) by sha256.
