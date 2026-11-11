# deep-65b: an Opus-led squad on the (6,5) cell (Nov 1-2, 2026, 22:39-01:07 UTC; stopped early by Doğa for budget)

Target: a bipartite graph with maximum degree 6 and diameter 5 on more than 684 vertices (table value 684, the Haar
graph of C6 x (C19:C3)). Third run on this cell, after handsoff-65 (Haiku squad, Opus only coordinating) and deep-65
(Opus-led, both leads closed or explained, no record).

## Result

**Record: 704 vertices** (+20 over the table, +2.9%). records/d6D5_n704_split_c11xm16.edges, sha256
85b88c13999f3b0f36798a43a57e5f8cca11e7bf93888f3e37a4232d1335aece.

- What it is: the regular voltage lift of the 2+2 base [[1,5],[5,1]] by G = Z11 x M16 = SmallGroup(176,23)
  (M16 = <x, y | x^8 = y^2 = 1, y x y^-1 = x^5>). Vertices A0_h, A1_h, B0_h, B1_h (h in G); edges A0_h - B0_h,
  A1_h - B1_h, A0_h - B1_{h e} (e in E1), B0_h - A1_{h e} (e in E2), with E1 = {(7,5,1), (9,7,0), (4,4,1), (6,0,0),
  (1,1,0)}, E2 = {(7,1,1), (8,0,1), (6,1,0), (9,0,1), (5,4,0)} ((a,i,j) = a x^i y^j). Equivalently: the degree-10 Haar
  graph H(G, E1 u E2) with every vertex split into an edge. Equivalently again: G = Z88 :_45 Z2, so it is a cyclic
  Z88-lift of an 8-vertex base (records/build_d6D5_n704_z88.py prints the 24 voltages and rebuilds the same edge set).
- Checks (I ran all of them; records/d6D5_n704_checks.txt): research/lifts/coordinator_check/apsp.c RESULT VALID at
  d = 6, D = 5 and RESULT INVALID at D = 4; score65 bad = 0; the self-contained builder (group from its formula, no
  table, no GAP) runs its own BFS (diameter 5); the group table used in the search equals the formula on all 176^2
  products.
- Not a Haar graph: the distance profile from an A0 vertex is (1, 6, 30, 140, 321, 206) and from an A1 vertex
  (1, 6, 30, 139, 321, 207), so no automorphism moves A0 to A1 and no group is regular on a side. Girth 6.
- Rebuild: `python3 records/build_d6D5_n704.py OUT.edges`.
- Unique in its group: the exact search over all lifts of this base by 176_23 finds exactly one solution class up to
  the symmetries (this one).

Who found it: the family, its closed form, the exact search and the verification are Opus's; the cost-0 point came
from a round-1 Haiku card (c1) that ran a tabu search over (E1, E2) with Opus's six conditions to rank groups for the
exact search. The exact search then re-found the same solution class, which also calibrated it.

No graph above 704 was found. The family appears saturated near m = 176 (see below).

## The idea: split Haar graphs (lifts of [[1,5],[5,1]])

Why this family. Handsoff-65 had annealed 2+2 base lifts at orders 171-180 and stopped at cost 4, but its own
calibration showed its search did not re-find the 684 record, which is itself a 2+2 lift (of [[3,3],[3,3]] by
C3 x (C19:C3)); so that floor said little. At (5,5) the record 384 came from an EXACT search of 2+2 lifts
([[1,4],[4,1]], beyond-haar-d5), 9% above the best Haar graphs there. The analogue here is [[1,5],[5,1]].

Closed form (tools/split15.c, NOTES.md). After normalising the two single edges to voltage 1, the voltage of the A1-B1
edge disappears (it is a relabelling), and the lift is determined by two 5-subsets E1, E2 of G. With E = E1 u E2,
diameter <= 5 iff
  C1 EE^-1 u (E1E1^-1)^2 = G,  C2 EE^-1 u (E2E2^-1)^2 = G,  C3 E^-1E u (E2^-1E2)^2 = G,  C4 E^-1E u (E1^-1E1)^2 = G,
  C5 E u E1E1^-1E1 u E1E1^-1E2 u E1E2^-1E2 u E2E2^-1E2 = G,  C6 E u E1E1^-1E1 u E2E1^-1E1 u E2E2^-1E1 u E2E2^-1E2 = G.
Checked against BFS on the built graphs: 300 random pairs on C11:Q16 and 2000 each on A5, C30 x C2, C25:C4, per-condition
counts identical, 0 mismatches (485 valid graphs among them). The binding conditions are C5, C6 (370 words each for m
elements); at m = 176 that is 47.6% of the word count, where the Haar record sits at 43.8%.

Exact search. E1 over symmetry classes of 5-sets (union-find over all 4-subsets of G \ {1} under Aut(G), translations
and inversion); for each E1, every E2 covering E1's deficits in C1 and C4 is enumerated by branching on the first
uncovered element; E1 is always the worse set (swap symmetry); the other four conditions are tested at the leaves.
Two exact speed-ups (capacity bound per node; list mode for the best E1 classes) made it 6x faster. Validation: brute
force over all C(176,5) partners agrees for six E1 (0 to 2.14M partners); the speed-ups give identical counts on a
1/40 sample; and on 176_23 it re-finds the tabu's solution class.

Exact results (runs/, tools/summ.sh; "best" = least total misses of C2, C3, C5, C6 among pairs meeting C1 and C4,
"-" = no pair meets C1 and C4 at all):

| group | n | result |
|---|---|---|
| 176_23 C11 x M16 | 704 | **1 solution class (the record)** |
| 176_17 C11:Q16 | 704 | none, best 2 |
| 180_21 C3 x (C15:C4), 180_6 C9:(C5:C4), 180_13, 180_22 | 720 | none, best 3, 5, 6, 6 |
| 189_12 | 756 | none, best 16 |
| 192_865, 909, 544, 105, 106 (round-2 tabu leaders) | 768 | none, best 6-16 |
| 172_1, 174_3, 176_27, 29, 33, 34, 35, 41, 178_1, 180_17, 27, 36, 182_3, 184_11 | 688-736 | none, - |

Tabu screens (rounds 1-3, Haiku cards, tabu15/tabu15f, 8-12 s per seed): every non-abelian group of orders 172-190 and
195-200 and 315 groups of order 192 (all 256 of the winner's shape C3 x P64, 59 sampled others, ids 1-127). Best costs
(total misses): 176: 0 (176_23), 2 (176_17, 174_1 at 696); 180: 4 (180_2), 5; 183 (C61:C3), 189: 7; 186: 8; 192: 6
(192_865, 909); 195-200: 13+; C13 x M16 (208, the winner's shape one step up): 37+.

## The two leads from handsoff-65

deep-65 had closed lead (b) exactly at 686 (cost 2 is the global optimum of the 1,6|1,6 hub family on SmallGroup(294,11),
the two missing elements are an inverse pair in the abelian core C7 x C7) and explained lead (a) (every edge of the 684
graph carries 44-83 damaged pairs that only nearby vertices can reroute; best 144). I did not repeat either. What this
run adds:
- deep-65's open hub cases: k = 5 on SmallGroup(290, 1..3) (n = 696) is closed: no solution (nothing passes the
  hub-level conditions); 16 of the 45 non-abelian groups of order 300 too (round-1 c3). k = 3 on 258_3, 258_4, 258_5
  (n = 688) is NOT finished: 0.09%, 12% and 6.4% of the leaves, no leaf passing the hub-level conditions in 1.7e10
  (round-1 c4); 258_3 needs ~170 CPU-hours as written. k = 5 at 305-315 was not run.
- Why the split family worked where the hub family stopped: both are lifts of small bases with a large symmetric
  group, but the hub family forces a C6 complement and, at 686, an abelian core of order 49; the split family has no
  hubs (all orbits regular), so it lives at n = 4m for any group, and the 2-groups x small cyclic factor that make
  C11 x M16 work are available. In both families the near misses are 1-2 missing elements in the binding cross
  conditions; the record family just has one group where that last miss closes.
- Lead (a)-type surgery was not tried on the 704 graph (deep-65's analysis of the 684 graph says every edge is
  critical; the 704 graph has the same kind of tightness: its exact neighbours in the family miss 2).

## Other structures tried (all short of 704 or far)

- "Split + hub orbits" (mcos types 1,1,6|1,1,6 and 1,1,6,6|1,1,6,6, n = 728): round-3 card c1 was stopped before reporting.
- Cyclic Z_n-lifts of the 8-vertex split base with all 17 voltages free (round-3 c4): calibrated (the record's
  voltages give cost 0 at n = 88; repairs from 1-2 changed voltages work) but random-start tabu does not reach 0 even at
  n = 88; n = 89-100: best 34-96. The group-lift (twisted) subfamily is the effective one.
- Other 2+2 bases (round-1 c2): a word-based tabu re-finds the 684 record only in the mirrored (Haar-type) subfamily;
  the general 9-voltage family stays at cost 10 at 720.
- Path-split Haar graphs (3+3 lifts, round-1 c5): 1755 bad pairs at 702. 4+4 lifts by dihedral groups (round-1 c6): 1505
  at 688.

## Squad rounds (research/squads/LOG.md)

- Round 1 (6 cards): the hit (c1), the 2+2 tabu calibration (c2), deep-65's hub cases (c3, c4), two wildcards (c5, c6).
- Round 2 (6 cards): the split family at orders 178-200 and 192 with more seeds; a 3.3x faster tabu (c6).
- Round 3 (4 cards): split + hubs (mcos), more seeds at 180 and 192, cyclic 8-vertex lifts.
Haikus did well on: running a tool on a precise family with a clear scorer (the hit), screening many groups, writing a
faster equivalent program with a self-check (c6), and the long exact hub chunks. They did less well when a card needed
a new evaluator for a new base (c4 round 3 built one but its tabu could not reach 0 even where a solution exists).

## Spend (tools/session_usage.py --since 22:39:12Z --arm deep-65b; research/squads/usage/deep-65b.jsonl)

Stopped at 01:07 UTC (2 h 28 min).

| model | messages | output tokens | units | share |
|---|---|---|---|---|
| Opus (me) | 186 | 285,904 | 1.640 | 97% |
| Haiku (16 runs, 3 rounds) | 653 | 685,645 | 0.058 | 3% |
| total | | | 1.698 | |

Most of the Opus cost is cache reads (61.8M tokens) over a long context, as in deep-65.

## Comparison with handsoff-65 and deep-65 (same cell)

| | handsoff-65 | deep-65 | deep-65b |
|---|---|---|---|
| structure | Opus coordinates, 28 Haiku runs search | Opus derives and searches, 7 Haiku runs | Opus derives a new family + exact search, 16 Haiku runs on its tools |
| wall clock | 5.5 h | 4.1 h | 2.5 h (stopped for budget) |
| spend (units) | 0.822 (34% Haiku) | 1.279 (2% Haiku) | 1.698 (3% Haiku) |
| record | none | none | **704** |

Plain verdict: the record came from the combination. Opus picked the family by analogy with the (5,5) record and the
failed calibration in handsoff's notes, derived the closed form and the exact search, and wrote the cards; a Haiku
running a simple tabu over that closed form hit the one solution class in the one group that has it; Opus verified it
and the exact search confirmed it. Neither earlier run had this family in closed form. On cost this run was the most
expensive per hour; on outcome it is the only one of the three with a record.

## Files

- records/: the 704 graph, two builders, checks, README.
- tools/split15.c (closed form + exact search + BFS validation + brute-force check), tools/runq.sh, tools/summ.sh,
  tools/nearmiss.py, tools/gap_tabaut.g and tools/gap_fast.g (group tables with automorphism generators).
- runs/: exact search outputs per group, the brute-force cross-checks.
- round1/, round2/, round3/: cards, scoreboards, Haiku code and notes. NOTES.md: derivations and the run log.

## Status at stop (01:07 UTC, Doğa stopped the run for budget)

Found: the 704 record (verified, pushed, records/). Left open:
- Exact split15 runs that were in progress and were killed: 174_1, 180_2 (tabu best 4), 180_14, 176_1 (no output kept).
  Not run at all: the other ~25 non-abelian groups of order 180 and most of 176, 184-190 with small Aut (est. 0.5-2 h each),
  and the order-192 groups beyond the five checked.
- Round 3: c4 finished (cyclic 8-vertex lifts, no zero). c1 (split + hubs via mcos), c2 (180, more seeds) and c3
  (192, more seeds) were stopped mid-card; whatever they wrote is in round3/<card>/ and round3/scoreboard.jsonl
  (no zero was on the scoreboard at the stop).
- deep-65's hub cases still open: k = 3 on 258_3..5, k = 5 at orders 300 (29 groups), 305, 310, 315.
