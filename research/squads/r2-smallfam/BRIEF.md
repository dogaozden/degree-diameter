# Squad round r2-smallfam (thm-smallfamilies resume, 2026-10-25): beat a cubic cell

## Goal
A bipartite cubic (Δ = 3) graph that beats one of these table values:
- **(3,10): more than 800 vertices, diameter 10** (main target: the table value is weak, 64% of the general cubic record);
- (3,9): more than 506 vertices, diameter 9;
- (3,7): more than 168 vertices, diameter 7.

A regular lift of a base with k vertices over a group G has k·|G| vertices. So at (3,10) a 3+3 base needs |G| ≥ 134,
a 4+4 base |G| ≥ 101; at (3,9) a 3+3 base needs |G| ≥ 85, a 4+4 base |G| ≥ 64; at (3,7) a 4+4 base needs
|G| ≥ 22, a 5+5 base |G| ≥ 17.

## Already known (do not repeat)
- Haar graphs (2-vertex base): none above 168 at (3,7) (complete); none for any group of order 254–320 at (3,9);
  none of order 400–452 at (3,10) (best cost 4). The main session is running (3,10) orders 453+.
- 2+2 base (`bases/b22.txt`) lifts over all groups: complete at (3,7) (Conder's 168, order 42, is the largest);
  none at (3,9) orders 127–170; none at (3,10) orders 201–228 (best cost 2, Z29 x| Z7, order 203).
- 3+3 bases at (3,7): b33_0 and b33_1 complete for orders 29–42; b33_2 (= K3,3) done for 29–36 only.
- b33_0 at (3,8) orders 49–56 and (3,9) orders 85–95: none (best cost 12).
- The 4+4 bases (all six, `bases/b44_*.txt`) and the 5+5 bases (all 15, `bases/b55_*.txt`) have never been searched.
  The lists are complete (basegen.py: 3, 6 and 15 connected multigraphs).

## Tools (repo /home/user/degree-diameter, folder research/theorems/smallfam, all compiled; run from that folder)
Set these two variables in every command so nothing is written outside your card folder:
`export OUTDIR=/home/user/degree-diameter/research/squads/r2-smallfam/cX SCRATCH=/home/user/degree-diameter/research/squads/r2-smallfam/cX/tmp`
(and `mkdir -p $SCRATCH`).
- **Lift annealing screen over every group of an order range** (GAP SmallGroups):
  `python3 lscreen.py bases/b33_0.txt 10 134 140 --secs 6 --abmin 1 --abmax 1000000`
  - writes `$OUTDIR/lscreen_b33_0_D10.tsv`: n, id, structure, |G^ab|, cost (lowest over seeds), voltages;
  - cost = number of (source, target) pairs at distance > D summed over one source per base vertex; 0 = a graph;
  - it skips groups that fail the rigorous rank and abelianization filters; `--abmin 1 --abmax 1000000` turns off
    the heuristic skips (keep it that way);
  - calibration: on `bases/b22.txt` at D = 7, order 42, it re-finds Conder's 168 graph in under 3 seconds.
- **Exhaustive lift search** over every group of an order range: `python3 allgroups.py 3 7 37 42 --base bases/b33_2.txt --cycles 4 --threads 1`
  (`--cycles` = number of free voltages of the base: 4 for 3+3, 5 for 4+4, 6 for 5+5). Writes
  `$OUTDIR/lift_<base>_D<D>.tsv`; column 8 = number of solutions, column 9 = best cost. Its "too-big" estimate is wrong
  for bases with more than 3 free voltages, so watch the clock and stop a run that is too slow.
- **Annealer directly** on one group: export a table with `python3 -c "import sys; sys.path.insert(0,'.'); from screen import export_table; print(export_table(N, I))"`,
  then `./lanneal TABLE BASE D SECONDS SEED 8 OUT` (prints `RESULT ... best=C ... voltages v1 v2 ...`; writes OUT on cost 0).
  Env TMAX, COOL, REHEAT, TARGP tune the annealing (see the header of lanneal.c).
- **Base files**: `bases/*.txt`: first line = number of base vertices, then one line per edge "w b" (free voltage)
  or "w b = e" (identity, a spanning tree). `python3 basegen.py n DIR [--simple]` writes all n+n bases.
- **Verification** (required before claiming valid=true): `python3 lift_edges.py N I BASE OUT.edges v1 v2 ...`
  (the voltages from the tsv), then `./verify/apsp OUT.edges 3 D`, which must print `RESULT VALID`.

## Rules
- 4 cores and 15 GB are shared by all of you and the main session, so:
  - THREADS=1 and `--threads 1`;
  - prefix heavy commands with `timeout 1200 nice -n 10`;
  - use at most about 1.5 GB of memory.
- Time box: 20 minutes of wall clock. Spend the first minutes running, not reading: the tools above work.
- No git commands. Do not edit anything outside your card folder `research/squads/r2-smallfam/cX/`; write your own
  scripts there.
- When done, append ONE line of JSON to `research/squads/r2-smallfam/scoreboard.jsonl`:
  `{"card": "cX", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <largest valid vertex count found, 0 if none>, "best_cost": <lowest cost seen>, "best_group": "<n,id structure and base>", "cell": "(3,D)", "valid": true|false, "next": "<one line>"}`
- Reply in at most 5 lines.

## Cards
- **c1** (3,10), base b33_0 over every group of order 134–145 (`--secs 6`), then three 60-second re-anneals
  (seeds 2–4, `lanneal` directly) on the three lowest-cost groups.
- **c2** (3,10), bases b33_1 and b33_2 (K3,3) over every group of order 134–142 (`--secs 6`); re-anneal the best two.
- **c3** (3,10), the six 4+4 bases b44_0 … b44_5 over every group of order 101–106 (`--secs 5`); re-anneal the best.
- **c4** (3,9), bases b33_1 and b33_2 over orders 85–95, then b33_0 over 96–100 (`--secs 5`).
- **c5** (3,9), the six 4+4 bases over orders 64–70 (`--secs 5`).
- **c6** (3,7), exhaustive: `allgroups.py --base` for b33_2 (K3,3) at orders 37–42, then the 4+4 bases at orders
  22–26 (in the order b44_5 (the cube), b44_0, …). Report how far you got and the best cost per base.
- **c7** (3,7), the 15 5+5 bases b55_0 … b55_14 over orders 17–25 with lscreen (`--secs 3`); exhaustive
  allgroups.py on the base and order that comes closest.
- **c8** wildcard: find an approach none of the cards above uses (they all lift 3+3, 4+4 or 5+5 bases with lscreen or
  allgroups). Ideas, take one or your own: (a) a general local search over cubic bipartite graphs at (3,7) with
  170 vertices (bipartite 2-switches, cost = pairs at distance > 7), seeded by Conder's 168 graph with two vertices
  spliced in (rebuild it with `python3 lift_edges.py 42 2 bases/b22.txt conder.edges 9 19 35`); (b) the five simple
  6+6 bases `bases/b66s_*.txt` at (3,7) orders 15–21; (c) non-regular graphs: max degree 3 allows some degree-2
  vertices; (d) anything else concrete you can score with apsp.
