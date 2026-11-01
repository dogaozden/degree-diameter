# deep-65b round 1 cards (Opus-written, 6 Haikus)

## Common rules (every card)
- Goal: a bipartite graph with maximum degree 6 and diameter 5 on MORE than 684 vertices (table value 684).
  Scorer: `research/squads/deep-65b/shared/score65 EDGES` (bad = unordered vertex pairs at distance > 5; 0 means
  diameter <= 5), then `research/squads/deep-65b/shared/apsp EDGES 6 5` (must print RESULT VALID). Edge files: first line
  n, then one edge "u v" per line.
- Group tables: `research/squads/deep-65b/groups/sg_<order>_<id>.tab` exist for every SmallGroup of orders 172-190 and
  195-200 except 192 (first line m, then the m x m table, identity = 0, then "ngen k" and k automorphism generators as
  image lists). `groups/sg_<order>_<id>.name` has the structure and |Aut|. Other orders: `research/squads/deep-65b/shared/gapw
  -c 'ORDER:=258; OUTDIR:="tabs";' research/squads/deep-65b/tools/gap_tabaut.g` (run it inside your folder; IDS:=[3,4]
  restricts the ids). For deep-65's hubk.c use shared/gap_tables.g the same way (plain table format, .txt).
- Machine: 4 cores, shared with 5 other workers and Opus's exact searches. Single-threaded only. EVERY command must
  finish in under 110 s: wrap heavy runs as `timeout 105 nice -n 15 CMD` and chain several short runs (longer commands
  get moved to the background and you would sit idle). Never start background processes, never `sleep`. At most 1.5 GB
  memory per process.
- Work only in your folder research/squads/deep-65b/round1/<card>/. No git commands. No edits outside your folder except
  appending to the scoreboard. Build with `gcc -O3 -march=native -o X X.c -lm`.
- Time box: 60 minutes from your start. Keep NOTES.md in your folder (what you ran, exact commands, results).
- Scoreboard: append ONE JSON line per new best and one at the end to research/squads/deep-65b/round1/scoreboard.jsonl:
  {"card": "c1", "idea": "<one line>", "code": "<path>", "command": "<exact>", "n": <vertices>, "score": <bad pairs or cost>,
   "valid": true|false, "next": "<one line>"}
- If you ever get score 0 with n > 684: run apsp, save the edge file in your folder, put it on the scoreboard at once.
- Final reply to Opus: at most 5 lines.

## Background: the [[1,5],[5,1]] lift family (Opus, tools/split15.c)
A lift of the 2+2 base [[1,5],[5,1]] by a group G of order m (n = 4m) is, after normalising, given by two 5-subsets
E1, E2 of G: A0_h ~ B0_h, A1_h ~ B1_h, A0_h ~ B1_{h e} (e in E1), B0_h ~ A1_{h e} (e in E2). With E = E1 u E2 it has
diameter <= 5 iff six covering conditions hold:
  C1 E E^-1 u (E1E1^-1)^2 = G,   C2 E E^-1 u (E2E2^-1)^2 = G,   C3 E^-1 E u (E2^-1E2)^2 = G,   C4 E^-1 E u (E1^-1E1)^2 = G,
  C5 E u E1E1^-1E1 u E1E1^-1E2 u E1E2^-1E2 u E2E2^-1E2 = G,   C6 E u E1E1^-1E1 u E2E1^-1E1 u E2E2^-1E1 u E2E2^-1E2 = G.
Cost = total number of missing elements over C1..C6 (verified against BFS). `shared/split15 TAB cost e1 e1 e1 e1 e1 e2 e2
e2 e2 e2` prints the six counts; `shared/split15 TAB edges <10 numbers> OUT.edges` writes the graph. Opus runs the EXACT
search of this family group by group (C11:Q16 = 176_17: best cost 2 so far, 704 vertices, bad 352).

## c1: rank the groups of orders 172-200 for the [[1,5],[5,1]] family (fast local search)
Opus's exact search costs 10-100 CPU-minutes per group, so we need to know which groups are worth it. Write a tabu
search over (E1, E2) with the six-condition cost above (incremental or plain recomputation with bitsets; read the table
format above; moves: replace one element of E1 or E2 by any other element, full neighbourhood scan, tabu tenure ~10,
restarts). Calibrate: on SmallGroup(176,17) it should reach cost <= 4 (Opus's exact optimum so far is 2). Then screen
EVERY non-abelian group of orders 172, 174, 176, 178, 180, 182, 184, 186, 188, 190, 196, 198, 200 (about 20-30 s per
group, 2 seeds) and write ranking.tsv (order, id, name, best cost, seconds). Abelian groups: skip (commuting walks
collide). Report the 10 best groups. Any cost 0: build the edges with split15, score65 + apsp, scoreboard at once.

## c2: a stronger search for the other two 2+2 bases, calibrated on the 684 record
handsoff-65's c1 annealed lifts of [[a,6-a],[6-a,a]] (a = 2, 3) at orders 171-180 with a BFS-based cost and found cost 4
at best, but it did NOT re-find the 684 record, which is a lift of [[3,3],[3,3]] by C3 x (C19:C3) (the index-2 subgroup
of C6 x (C19:C3); find its SmallGroup id among the 5 groups of order 171 with GAP). So its search was too weak to judge
the family. Task: (1) write an evaluator for lifts of a 2+2 base that precomputes, once, the list of non-backtracking
base walks of length <= 4 between same-side base vertices as words in the dart voltages (A0-A0, A0-A1, A1-A1, B0-B0,
B0-B1, B1-B1), so the cost of a voltage assignment is computed from words, not BFS; check it against BFS (score65 on the
built graph) on random voltages; (2) tabu over single-voltage changes; (3) calibrate: re-find cost 0 at order 171 on
C3 x (C19:C3) with base [[3,3],[3,3]] (report time to solution over several seeds); (4) if calibration works, screen
the non-abelian groups of orders 172-180 with a = 2 and a = 3. Report calibration success and the best cost per order.

## c3: deep-65's unfinished hub cases, k = 5 (exact, hubk.c)
deep-65 (its notes: research/squads/deep-65b/prior/deep65_NOTES.md and deep65_REPORT.md) defined "Haar degree 5 + hubs of size k + hub graph of degree 6-k", n = 2m + 2m/k, with an exact program hubk.c
(research/squads/deep-65b/shared/hubk.c; usage in its header; `hubk TABLE K ex`). For k = 5 the hub-hub relation is a
perfect matching. Not done: k = 5 on SmallGroup(290, 1..3) (n = 696; deep-65: "every group of order 290 has a normal C5,
R = a coset of it"), and nothing at the larger k = 5 orders: 295 (n = 708), 300 (720), 305 (732; includes the Frobenius
group C61:C5), 310 (744), 315 (756). Task: run `hubk TABLE 5 ex` (split long runs with NPROC PROC so each command is
< 110 s, or report the estimated total) on every non-abelian group of these orders that has a subgroup of order 5,
smallest n first. Validate one random state first (`hubk TABLE 5 rand 200 1` must print 0 mismatches). Report per group:
solution yes/no, best missing count, run time. Any solution: build and check the graph (hubk prints/writes edges; see its
source), score65 + apsp.

## c4: deep-65's unfinished hub cases, k = 3 on SmallGroup(258, 3), (258, 4), (258, 5) (exact, hubk.c)
Same family as c3 with k = 3 (n = 688). deep-65 closed 258_1 and 258_2 (best 4) but not 258_3, 258_4, 258_5, where the
order-3 subgroup is normal and the hub-hub relation R has 102,340 choices in 1190 orbits. Task: export the tables
(shared/gap_tables.g, plain .txt), validate (`hubk TABLE 3 rand 200 1`: 0 mismatches), estimate the run time
(hubk has COUNT=1 in deep-65's notes: it counts leaves without testing; check the source), then run as far as the time box
allows in chunks of < 110 s using NPROC PROC splits (record which chunks finished). If a full run is far out of reach,
say so with the estimate and give the best missing count over the chunks you ran.

## c5: wildcard: "path-split" Haar graphs (a new 3+3 family)
The [[1,5],[5,1]] family is a degree-10 Haar graph H(G, E1 u E2) with each vertex split into an EDGE. Generalise: split
each vertex of a Haar graph into a PATH of 3 vertices. Side X vertex x_h becomes A0_h - B0_h - A2_h, side Y vertex y_h
becomes B1_h - A1_h - B2_h (A0, A2, A1 on side A; B0, B1, B2 on side B; n = 6m, each vertex degree 6: ends have 1 path
edge + 5 external, middles 2 + 4). External edges: A0_h and A2_h to B1/B2 (5 each), B0_h to A1 (4), i.e. a 3+3 base
with blocks A0: B0 1, B1 a, B2 5-a; A2: B0 1, B1 5-a, B2 a; A1: B0 4, B1 1, B2 1. Lift it by a group of order m with
n = 6m > 684, so m >= 115 (115-130). Task: write the generic word evaluator or a BFS evaluator for 3+3 lifts (check it
with score65), anneal/tabu the voltages for a = 1, 2, 3 on non-abelian groups of orders 115-130 (GAP exporter above),
and report the best cost per order. Compare with the walk counts: compute the number of non-backtracking walks of length
<= 4 from each base vertex to each same-side base vertex (the minimum over targets bounds m), and say whether the family
has room above 684.

## c6: wildcard: find an approach none of the other cards uses
The other cards: c1 tabu ranking of groups for the [[1,5],[5,1]] split family; c2 word-based tabu for [[2,4],[4,2]] and
[[3,3],[3,3]] lifts calibrated on the 684 record; c3 hub family k = 5 exact; c4 hub family k = 3 on 258_3..5 exact;
c5 path-split Haar graphs (3+3 lifts). Already closed by earlier runs: every Haar graph on 686-900 vertices; the
hub family 1,6|1,6 at 686-728; surgery on the 684 graph (best 144 bad pairs at 686, every edge of it is critical);
GH(5,5)/GQ(5,5) quotients and covers; bi-coset graphs |H| = 2, 3 at 722-766 (floor 12). Propose ONE different
construction for > 684 vertices, write it as code, score it with score65, and report the best bad count with a one-line
reason why it could or could not reach 0. Ideas you may use or ignore: splitting the vertices of a Cayley graph (not a
Haar graph) of degree 10 into edges; graphs from finite geometries over F_7 (686 = 2 x 7^3); 2+2 lifts in which one
parallel class is replaced by a non-regular orbit (hubs).
