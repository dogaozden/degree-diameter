# Squad bh5-r3: common rules (job beyond-haar-d5)

Goal: bipartite graphs, max degree Δ, diameter exactly 5, MORE vertices than our records: (Δ,D) = (5,5) > 354 and
(7,5) > 1,152. Haar graphs (2-vertex base lifts) of every relevant group were already searched exhaustively; do NOT run
Haar searches. Everything below is a non-Haar construction.

Tools (all in /home/user/degree-diameter/research/beyond-haar-d5, already compiled; read the header of each source):
- `./vl BASE GROUP` (src/vl.c): annealer over voltage lifts of a bipartite base multigraph by a group. Lift vertices
  (v,h); base edge (a,b,g) gives (a,h)~(b,h*g). Cost = number of uncovered (source, target) pairs; cost 0 <=> lift has
  diameter <= 5. Env: D=5, SECS, ITERS (steps per annealing run), SEED, T0, T1, SWAP (prob. of base 2-switch moves),
  INC=1 (incremental evaluation, much faster for bases with > 30 vertices; no SWAP), TABU, OUT (best solution file).
  Prints `RESULT best <cost> ... vertices <b*m> [DIAMETER_OK]`.
  Base file: "b E" / b side bits (0/1) / E lines "u w [voltage]" (multi-edges allowed). Base degree = lift degree.
- Groups: `gap -q -c 'ORDER:=60; OUTDIR:="<your folder>/groups";' src/gap_tables.g` writes sg_<order>_<i>.txt (table
  for vl) and .name (structure) for all SmallGroups of that order; add `IDS:=[3,5];` to limit. mkdir the folder first.
  Write group tables into YOUR card folder (other cards run at the same time).
- `python3 src/rand_base.py k DELTA SEED OUT [MAXMULT]`: random connected DELTA-regular bipartite multigraph, k per side.
- `python3 src/gq_base.py q J SEED OUT [DOUBLE]`: W(q) incidence graph (2(q+1)(q^2+1) vertices, degree q+1) plus J
  random point->line matchings (DOUBLE=1: J parallel copies of one matching). Needs gq/gq_q{q}.bin (q=2..5 present).
- `./ga EDGES` (src/ga.c): annealer on a whole graph by degree-preserving 2-switches, cost = ordered pairs at distance
  > D. Env: D, DELTA (max degree, REQUIRED), SECS, SEED, T0, T1, FOCUS, ADD, OUT. `python3 src/grow.py IN OUT DELTA K SEED`
  adds K vertex pairs to a regular graph by deleting K matchings of size DELTA.
- Record graphs (edge lists "n" then "u v"): graphs/rec354.edges, graphs/rec352.edges (Δ5), graphs/rec1152.edges,
  graphs/rec1140.edges (Δ7).
- Verify any cost-0 lift: `python3 src/export_lift.py SOL GROUP edges.txt && ./apsp edges.txt DELTA 5` must print
  RESULT VALID with diameter=5 (all-pairs BFS, no symmetry assumed).

Machine rules: 4 cores shared by about 7 processes. Run ONE heavy process at a time, always as `timeout 900 nice -n 10 <cmd>`
(or shorter), at most 1.5 GB memory. No git commits. Do not edit anything outside your card folder
research/squads/bh5-r3/<card>/ (create it; put scripts, logs, solutions there). Time box: about 20 minutes total.

Scoreboard: append ONE line of JSON to research/squads/bh5-r3/scoreboard.jsonl when you finish:
{"card": "cN", "cell": "(7,5)", "idea": "<one line>", "code": "<path>", "command": "<exact>", "target_n": <vertices
tried>, "best_cost": <lowest cost reached at that size>, "valid": true|false (true only if apsp printed RESULT VALID with
more vertices than the record), "score": <vertex count if valid else 0>, "next": "<one line>"}
If you find a VALID graph above the record, also save SOL, group file and edges in your folder and say so first.
Reply to the coordinator in at most 5 lines.

## Round-3 tool: exhaustive bi-coset (coset) graphs, research/beyond-haar-d5/coset/ (cd there to run)
A group G, subgroups H, K of order h (one per conjugacy class), vertices = right cosets of H (side A) and of K
(side B), Hx ~ Ky iff x y^-1 in S, S a union of double cosets HgK. Degree = sum of the chosen double cosets'
contributions; G is transitive on each side, so cost = vertices missed within distance 5 by the two base vertices
(two BFS); cost 0 = diameter <= 5. dcenum tries EVERY union with total degree Δ (capped at 2M unions per (H,K)).
- `./sweep.sh ORDER h Δ` : every SmallGroup(ORDER, i), every pair of classes of subgroups of order h (h prime is
  fast). Appends one RESULT line per (group, H, K) to logs/sweep_h<h>_d<Δ>.txt and prints "HIT ..." for cost 0.
  Fields: RESULT <file> tested <unions> solutions <count> best <cost> vertices <N> set <ids>.
  (vertices N = 2|G|/h.) Use a different ORDER per call; never run two sweeps of the same ORDER at once.
- `./run_group.sh NAME "GAP expression" h Δ` : the same for one constructed group (e.g. "DirectProduct(
  AlternatingGroup(5), AlternatingGroup(5))"), all pairs of classes of subgroups of order h; results in
  logs/NAME_h<h>_d<Δ>.result.
- Known so far: PSL(2,17), h=4, Δ=7: 1224 vertices, best cost 14 (closest (7,5) result); A6 h=2 / S6 h=4 at 360
  (Δ=5): best 20; SmallGroups of order 546 with h=3, Δ=5: best 102.
- NrSmallGroups(n) in GAP gives the group count; skip orders with more than about 300 groups unless told otherwise.
- A cost-0 graph: its edges are copied to coset/logs/*.edges; run ../apsp on it (Δ, 5) and report first.
