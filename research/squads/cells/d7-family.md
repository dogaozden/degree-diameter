# D = 7 family: tonight's hexagon constructions carried to the other D = 7 cells (job d7-family)

Session: claude/d7-family-hexagon-mrr6hp, 2026-10-25 (16:13–22:30 UTC). Opus with Haiku squads (rounds d7fam-r1, d7fam-r2,
research/squads/LOG.md). Tools in research/d7family/.

The three constructions (all on the split Cayley hexagon H(q)):
- mirrored surgery (research/theorems/MIRRORED_SURGERY.md, research/cell147/mirror/): a point set R' and a bijection
  sigma with R' non-collinear, sigma(R') non-concurrent and sigma a local duality at every point of R'; frees R' on a
  non-friendly transition;
- typed levels (research/squads/cells/d16D7.md): levels of type H or H^D, identity matchings on friendly transitions
  (types differ), any non-collinear / non-concurrent set freed there;
- relaxed friendly sets (research/d15D7b/RELAXED.md): collinear (concurrent) pairs allowed in a friendly freed set when
  hubs are wired to cover elements incident with the partner.

## Results

| cell | master | this job | gain | construction | check |
|---|---|---|---|---|---|
| (16,7) | 4,052,108 | **4,053,576** | +1,468 | typed HDHDH of H(13) + mirrored 813 on the four non-friendly transitions + relaxed point sets | apsp_w all pairs VALID |
| (14,7) | 1,789,588 | **1,789,917** | +329 | typed HDHDH of H(11) + mirrored 768 + relaxed line and point sets | apsp_w all pairs VALID |
| (10,7) | 225,152 | **225,156** | +4 | mirrored surgery, 3 copies of H(8), mirrored set 231 (squads r1 c5, r2 c1) | apsp_mt all pairs VALID |
| (13,7) | 1,064,472 | — | | three levels: typed levels give nothing; the H(11) mirrored set is add-maximal (exhaustive scan) and two squad cards did not improve it | |
| (11,7), (12,7) | 413,180, 693,500 | — | | H(9) spread construction; typed / relaxed cannot beat it (bound below) | |
| (7,7), (9,7) | 23,598, 118,238 | — | | three levels; the H(5), H(7) mirrored sets are add-maximal and 1-out/2-in optimal (exhaustive scans), four squad cards did not improve them | |
| (15,7) | 2,501,124 | not touched | | another session works on it | |

Intermediate (16,7) value 4,053,490 = 10·402,234 + 2·(14,762 + 813): master's typed sets with the mirrored 813 set on the
non-friendly transitions (the +1,382 estimated in research/cell147/typedmirror/README.md); its full check was stopped at
7 % (540 of 7,918 batches) in favour of the relaxed graph, which contains it as a special case.

## Which construction applies where

- **Typed levels need at least five levels.** With three levels (cells (7,7), (9,7), (10,7), (11,7), (13,7), one
  matching per class) the matchings form a 3-cycle, so one transition is always non-friendly, and hubs need a free slot
  in every level: n = 3·|I(H(q))| + 2·min(|R_H|, |R_L|, |R'|) = the mirrored value. Only larger mirrored sets help.
- **Five levels (types HDHDH) is the only good pattern** for (14,7) and (16,7): with two adjacent D levels some level
  has no friendly outgoing transition. In HDHDH all six friendly transitions are bottlenecks
  (KB = N + min(P01, L12, P23, P41, L34 + L30 − N), KA = N + min(L30, L12, P23, L34, P01 + P41 − N), N = |R'|), so the
  covers of every relaxed set must come from the other bottleneck sets (no private covers as in (15,7)).
- **H(9) cells (11,7), (12,7):** H(9) is self-dual and every matching there is already a duality, which is what typed
  levels emulate; the records use the spread construction (7,300 freed points per level and shift, cap 14,600 hubs per
  side at (12,7), research/squads/cells/d12D7.md §3). Relaxed sets cannot beat it: the collinearity graph of H(q) has
  degree q(q+1) and smallest eigenvalue −(q+1), so a point set in which every point is collinear with at most one other
  has at most N(1 + q + 1)/(q + 1)² points (Hoffman-type bound for induced subgraphs of maximum degree 1), i.e.
  66,430·11/100 = 7,307 at q = 9, against the 7,300 already freed. No new value there.

## (16,7): 4,053,576

Five levels H D H D H of H(13) (types as in d16D7.md), matchings j -> j+1, j+2. Friendly transitions (identity):
0->1, 2->3, 4->1 free point sets P01, P23, P41; 1->2, 3->4, 3->0 free line sets L12, L34, L30. Non-friendly
transitions 0->2, 2->4, 4->0 (sigma) and 1->3 (sigma^-1) free the mirrored set R' (813 points, sigma from
research/frontier/sols/d16D7_hex13_mirror813_n4025592.sol, cell-14-7 session; copied to this branch). Free slots:

| level | type | A-slots (line-side hubs) | B-slots (point-side hubs) |
|---|---|---|---|
| 0 | H | P01 + R' (0->2) | sigma(R') (4->0) + L30 |
| 1 | D | L12 + sigma(R') (1->3) | P01 + P41 |
| 2 | H | P23 + R' (2->4) | L12 + sigma(R') (0->2) |
| 3 | D | L34 + L30 | P23 + R' (1->3) |
| 4 | H | R' (4->0) + P41 | L34 + sigma(R') (2->4) |

KB = 813 + min(P01, L12, P23, P41, L34 + L30 − 813), KA = 813 + min(L30, L12, P23, L34, P01 + P41 − 813), n = 10·402,234
+ KB + KA. With master's sets (P = R_H = 14,762, L = R_L = 14,823) this is 4,053,490. Relaxed point sets (dpack
from R_H with pairing masks, research/d7family/hd5_masks.py): P01 14,787 (29 collinear pairs), P23 14,823 (61 pairs),
P41 14,800 (38 pairs); line sets unchanged. KB = 15,600, KA = 15,636, n = 4,053,576. Hub graph: 11 random matchings
between 15,600 line-side and 15,636 point-side hubs (hubgen.py seed 1: 171,600 edges, line-side degree 11,
point-side degree 10 or 11), all same-side distances <= 6 in the hub graph alone (hubsame.py).

## (14,7): 1,789,917

The same layout on H(11) with the mirrored 768 set of the (14,7) 1,774,632 graph. Here the line sets bind (master's
R_L = 8,246 < R_H = 8,645). First version (checked, 1,789,858): relaxed line sets L12 8,381 (138 concurrent pairs),
L34 8,390 (156), L30 8,388 (333), point sets = R_H; KB = KA = 768 + 8,381 = 9,149. Then two coupled rounds
(research/d7family/hd5_grow.sh: P23 || P01 -> P41, then L12 || L34 -> L30, 300 s each, protect lists keep every cover
in use): the point sets, which have slack here, become 1-defective too (8,753-8,827 points, 214-230 pairs), which gives
the line sets more covers: L12 8,415, L34 8,406, L30 8,467 after drops; KB = 9,183, KA = 9,174,
n = 1,771,560 + 18,357 = 1,789,917. A third round (450 s per set) left L12, the binding set, at 8,415 and moved L34 to
8,410 (at most +4), so it was not built.

## The relaxed sets on five levels: what limits them

A pair {r, x} in a friendly set needs, for both orders, a colour-0 cover (a B-slot at the source level on an element
incident with x) and a colour-1 cover (an A-slot at the target level incident with x). On five levels these slots belong
to the other friendly sets and to R' / sigma(R'):

| set | colour-0 covers (source level, B-slots) | colour-1 covers (target level, A-slots) |
|---|---|---|
| P01 | L30, sigma(R') | L12, sigma(R') |
| L12 | P01, P41 | P23, R' |
| P23 | L12, sigma(R') | L34, L30 |
| L34 | P23, R' | R', P41 |
| L30 | P23, R' | P01, R' |
| P41 | L34, sigma(R') | L12, sigma(R') |

Two demand types share a slot level (colour 1 of P01 and P41 at level 1; colour 0 of L34 and L30 at level 3), and a
pair whose two elements meet on a cover element wants the same slot twice. hd5_masks.py therefore gives dpack (a) a
pairing mask (elements with a cover option of both colours), (b) a competitor mask (options already used by the
competitor's partners are removed) and (c) forbidden meeting cells (dpack.c FORBID: no pair may meet on a cover
element). With these the hub assignment (tmL_build.py assign) serves every pair; without (b) and (c) the first (14,7)
attempt left 203 pairs unserved.

The masks are the bottleneck. A non-collinear point set of H(q) meets at most |P|(q+1)/N of the lines (58.6 % at
q = 11, 51.4 % at q = 13), and the same holds dually, so only about half of the elements can be paired at all, and the
meeting cell must avoid another half. Without masks dpack grows the sets much further in the same time (H(11) lines
8,246 -> 8,776 with 1,109 pairs; H(13) points 14,762 -> 15,301 with 1,301 pairs, 150 s each); with masks it gains
+135 to +145 (H(11) lines; +160 to +221 after two coupled rounds) and +25 to +61 (H(13) points). In the
seven-level (15,7) layout non-bottleneck friendly sets provide private covers (research/d15D7b/README.md); five levels
have none, since every level has exactly one friendly outgoing transition except level 3 and one friendly incoming
except level 1.

## Checks

- research/d7family/apsp_w.c: apsp_mt.c (BFS from every vertex, no symmetry; simple, max degree, bipartite, connected,
  exact diameter) with 512 sources per batch (one cache line per vertex), sources sorted by colour so that each BFS step
  scans only one colour class, push steps while the frontier is below n/64, and saturated vertices skipped in pull
  steps. Validated against apsp_mt: (9,7) 118,238 (VALID, diameter 7) and a copy with 30 random edges deleted
  (diameter 9 in both, for every push threshold PUSHDIV = 1, 2, 64, 10^8); (10,7) 225,154 (VALID in both).
- Every solution rebuilds byte-identically (sha256 of the edge list in the check files), and tmL_build.py build
  re-checks every hypothesis: R' non-collinear, sigma(R') non-concurrent, local duality at every point of R', (R1) and
  (R2) for every pair, hub slots distinct, degrees.
- hubfar.c (from research/d15D7b): BFS from all hubs and both vertices of every paired element (the pairs not covered by
  the theorems), depth 7: 0 far pairs for (14,7) and (16,7).
- Full runs here (4 threads, shared machine): (14,7) 1,789,858 in 30 min, (16,7) 4,053,576 in 70 min (apsp_w);
  (10,7) 225,156 in 53 s (apsp_mt). The plain apsp_mt would take about 9 h for (16,7) on 4 threads.

## Squad rounds (research/squads/LOG.md)

r1 (8 cards): mirrored extensions for q = 5, 7, 8, 11, 13 and plain sets for H(11) lines and H(13) points/lines. Only
c5 (q = 8, full line pool, many proposals, T 0.1) gained: 230. r2 (5 cards) applied that recipe to the others: q = 8
reached 231; q = 5, 7, 11, 13 did not move (81, 295, 768, 813). The plain sets (c6–c8) did not beat master's symmetric
sets.

## Tried and negative

- **Hubs that skip a level (three levels).** On the typed three-level (13,7) graph (H D H; R_H at 0->1, R_L at 1->2,
  mirrored R' at 2->0) the levels 0 and 1 have 8,645 and 8,246 free A-slots but level 2 only 768, so a line-side hub
  with many slots in levels 0, 1 and none in level 2 would raise the hub count if its neighbours reached all of level 2
  within 6. Measured (research/d7family/cov.c, BFS on the main graph): a level-0 slot reaches every point of level 2
  but only about 14 % of its lines, so greedy set cover over 600 sampled slots still leaves 230 lines uncovered after 30
  slots (a hub has at most 12). Dead; the same count rules out skipping a level on five levels (about 8 % of the lines
  of the skipped level per slot).
- **Partners in the mirrored set.** The proof of RELAXED.md goes through for a non-friendly transition j -> j+k with
  matching sigma (local duality at every point of R') when R' may contain collinear pairs {x, x'} (each point at most
  one partner; sigma(R') then has the same pairs as concurrent lines): the only routes that fail are (a) x to a point b
  at distance 5 from sigma(x) through the line sigma(x'), repaired by the line-side hub of the A-slot (x, j) if its
  level-(j+k) slot is a point on sigma(x'), and (b) sigma(x) to a line a at distance 5 from x through x', repaired by
  the point-side hub of the B-slot (sigma(x), j+k) if its level-j slot is a line through x'. On typed levels the
  friendly sets supply such covers. But no partner can be added to the current configurations: research/d7family/
  probe3.py counts, for every candidate (a, y, M) (y collinear with exactly one base point a, line M meeting exactly
  the spread line that becomes sigma(a)), whether the base points of each type at distance 4 / 6 from y fit into the
  usable spread lines of that type at distance 4 / 6 from M: 0 feasible at q = 5 (2,060 candidate y, 3,300 lines M),
  q = 7 (15,874 y, 18,535 M), q = 8 (15,338 y, 35,051 M) and q = 11 (99,060 y;
  partnerscan.py); the q = 13 scan did not finish in the session. A partner would have to be annealed together with the
  extra points (as an extra point that pins sigma of its base point instead of wasting a spread line).
- **Exhaustive moves on the mirrored configurations.** research/d7family/addscan.py tests every (extra point, line) pair
  for a single addition by the exact type condition (validated: after deleting the last extra point of the q = 5 state
  it finds exactly that pair, and nothing else). No single addition exists at q = 5 (state 81), q = 7 (295), q = 8
  (231), q = 11 (768) or q = 13 (813; 47,373 candidate points x 74,528 candidate lines, 25 min). swapscan.py (remove
  one extra, add two) finds no improvement at q = 5, 7, 8: after removing an extra point only 1-27 single additions
  exist and no two of them are compatible; MODE=base (remove a base point, add two) finds none at q = 5, 7, 8 either
  (at q = 5 no single addition exists after removing any base point). The configurations are local optima for these
  moves, as the annealers suggested.
- **More 1-defective growth on five levels at q = 13:** with master's line sets the H(13) line sets gain nothing in
  300 s (0 pairs; every candidate line is blocked), the point sets gain 25-61 each; competing P01 / P41 partners for
  level-1 covers cost 38 + 39 drops when both use the same pair orbit.

## Next steps

- Co-designed covers on five levels: choose line sets that contain a line through every partner of a good unmasked
  point set (and dually), instead of masking the pairs by the current sets. The unmasked runs show the room (+539
  points at q = 13); each element gained in all six sets is +2. Forcing a prescribed line through a point costs about
  half a line in a non-concurrent set, so this only pays if the covers are designed jointly.
- Partners in the mirrored set (above) inside the mirrored annealer (mirror_sa5/6 with a move "add y collinear with a
  base point a, pin sigma(a) to the spread line meeting M"); each partner is +2 on every cell that uses that q.
- q = 8 mirrored set: still moving under the annealer (229 -> 230 -> 231 in two rounds).

## Files

research/d7family/ (this job):
- tmL_build.py: research/d15D7b/tm3_build.py for any odd number of levels (here five; header typedmirrorL). assign /
  sethub / build; build re-checks every hypothesis and writes the edge list and the hub/paired BFS sources.
- hd5_masks.py: pairing mask, protect list, forbidden meeting cells for one friendly set of the five-level layout.
- hd5_grow.sh: masks + dpack for a list of sets; hd5_drop.py: assignment with drops of unserved pairs, prints n.
- dpack.c: research/d15D7b/dpack.c plus the FORBID option. hubgen.py, hubfix.py, hubfar.c: from research/d15D7b.
- hubsame.py: same-side distances in a hub graph. apsp_w.c: the all-pairs checker above.
- addscan.py, swapscan.py: exhaustive single additions and 1-out / 2-in moves for mirrored configurations; probe3.py,
  partnerscan.py: partner points (the same test; partnerscan hashes on the zero-slack types and agrees with probe3,
  e.g. 375,841 feasible partners at q = 5 when only 3 extra points are kept); hexmod.py: copy of research/cell147/mirror/hexmod.py (cell-14-7 branch) for these three.
- cov.c, mkmain3.py: the skip-a-level coverage experiment (main graph of the typed three-level construction).
- checks/, configs/ (q = 8 mirrored states)

Solutions (research/frontier/sols/): d16D7_hex13_typedrelax_n4053576.sol (names d16D7_hex13_mirror813_n4025592.sol),
d14D7_hex11_typedrelax_n1789917.sol and the superseded d14D7_hex11_typedrelax_n1789858.sol (both name
d14D7_hex11_mirror768_n1774632.sol), d10D7_hex8_mirror231_n225156.sol,
d10D7_hex8_mirror230_n225154.sol (superseded).

## Handoff (end of session, 2026-10-25)

For the coordinator, in order:
1. (16,7) 4,053,576: research/frontier/sols/d16D7_hex13_typedrelax_n4053576.sol, check
   research/d7family/checks/d16D7_hex13_typedrelax_n4053576.check.txt (rebuild with tmL_build.py, byte-identical edge
   list; full all-pairs apsp_w VALID; apsp_mt would take about 9 h on 4 threads).
2. (14,7) 1,789,917: research/frontier/sols/d14D7_hex11_typedrelax_n1789917.sol, check file of the same name
   (full all-pairs apsp_w VALID, rebuild byte-identical). Earlier version 1,789,858 (d14D7_hex11_typedrelax_n1789858.sol, full check VALID).
3. (10,7) 225,156: research/frontier/sols/d10D7_hex8_mirror231_n225156.sol (multi_sol.py build; apsp_mt VALID).
Nothing new for (7,7), (9,7), (11,7), (12,7), (13,7); (15,7) not touched. The reasons are above (three levels: only
the mirrored set counts and it is add-maximal at every q tried; H(9): the 1-defective bound 7,307 against 7,300).
