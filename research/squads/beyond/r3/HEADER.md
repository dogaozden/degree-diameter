# Squad "beyond", round 3: shared header (read this first, then your card)

Job new-cells-beyond (Opus director, 2026-10-26, branch claude/new-cells-beyond-etos3t). Goal: the FIRST values for 48
cells outside the 2013 bipartite degree-diameter table: Δ = 17..20 at D = 3..10, and D = 11, 12 at Δ = 3..10.
A value = a bipartite graph of maximum degree ≤ Δ and diameter ≤ D that we built and checked. Repo root:
/home/user/degree-diameter (all paths below are relative to it).

## Machine rules (4 cores, 15 GB, shared by ~18 cards and the director)
- Single thread (THREADS=1, no OpenMP threads > 1). Every heavy command: `timeout 900 nice -n 10 <cmd>`.
- Memory ≤ 1.5 GB per process unless your card says otherwise. Never start more than one heavy process at a time.
- No git commands that change anything (no add/commit/checkout/stash). Reading other branches is fine:
  `git show origin/<branch>:<path>`.
- Write only inside your card folder research/squads/beyond/r3/<card>/ (create it). Build binaries there.
- Time box: about 25 minutes of work. Stop earlier if done.

## Scorer / checkers (a card's "valid" must come from one of these)
- Any edge list: `cc -O2 -o apsp research/lifts/coordinator_check/apsp.c` then `./apsp EDGES d D`
  (EDGES = first line n, then one "u v" per line, vertices 0..n-1). Prints `RESULT VALID ...` with the exact diameter.
  Fine up to ~150k vertices (time ~ n^2·Δ/64). Above that: say so, and check a smaller instance of the same
  construction fully plus BFS from ~50 random vertices of the big one.
- Haar graphs (solution files `d D sl p n ...`): `python3 research/frontier/build_haar2.py SOL` (≤ 2M vertices) or
  `cc -O3 -o hcsl research/frontier/haarcheck_sl.c && ./hcsl SOL` (SL), `research/structured/tools/haarcheck_psl.c` (PSL).
- Upper bound for every cell: bipartite Moore bound M_b = 2(1+(Δ−1)+…+(Δ−1)^(D−1)); for D ∉ {3,4,6} it is M_b − 6
  (Feria-Purón & Pineda-Villavicencio, DAM 2012, Prop. 6.4).

## Scoreboard (one JSON line per card, appended at the end; more lines allowed if you score several cells)
Append to research/squads/beyond/r3/scoreboard.jsonl:
`{"card": "c07", "cell": "18,5", "idea": "<one line>", "code": "<path>", "command": "<exact command that rebuilds the graph>",
"score": <vertices>, "valid": true|false, "check": "<path of the checker output you saved>", "next": "<one line>"}`
Save every valid graph you claim as `research/squads/beyond/r3/<card>/<cell>_n<vertices>.edges.gz` (gzip of the apsp
input) or, if too big to save, the exact builder command. Reply to the director in at most 5 lines.

## Already found / already ruled out (do not redo; earlier work in research/squads/beyond/r1/, r2/)
Current best checked values: research/frontier/beyond/BEYOND_TABLE.md (table) and results.py. In short:
- D=3, 4: done (Moore or POLISHED.md theorems). D=5: (17,5) 33,792 (floor), (18,5) 47,600 (MDM), (19,5) 52,428 (DM on
  W(16)), (20,5) 75,000 (route chart over F5; round-2 card d01 pushing). (13,5) 11,700 (MDM on W(8), a record).
- D=6, 7: formula families (H(q), Theorem D, polygon covers), cards r1/c08, r1/c09.
- D=8..12 at Δ ≥ 5: Haar graphs from the director's queue (haar_big / haar_sym); cards do not run these cells.
- D=11/12 small Δ: (3,11) 1,008 (Haar PSL(2,7)×Z3), (3,12) 1,320 (Haar PSL(2,11)), (4,11) 18,480 (Haar SL(2,11)×Z7,
  S = {e} ∪ one orbit of size 3), (4,12) 50,160 (SL(2,11)×Z19). Near misses: (3,12) SL(2,11) cost 16, PSL(2,13) cost 24
  (annealing, r1/c12 logs); (3,11) metacyclic orders 350–400 fail exhaustively (r1/c11); voltage lifts of small cubic
  bases (r2/d07, r2/d08) and AGL/PGL/heis sweeps (r1/c11 sweep_specs*_out.txt) found nothing larger.
- Ruled out: see r1/HEADER.md and r2/HEADER.md; route charts with plain letters at (17,5)/(19,5) and 9×F2 at (18,5)
  did not converge in round 2 (CPU-starved; not proofs).
- The machine is busy with the director's billion-vertex Haar checks: keep to ONE single-threaded heavy process.

## Theorem docs (read only what your card needs)
- research/theorems/POLISHED.md is on branch origin/claude/thm-polish-2oddll (fourth hat §2, Theorems A/B/C §3–5,
  Theorem D/R §6–7, Haar lemma §8): `git show origin/claude/thm-polish-2oddll:research/theorems/POLISHED.md`.
- research/theorems/D7_HEXAGON.md on origin/claude/d7-hexagon-theorems-4w1prt (level graphs, hubs at D = 7).
- research/d10D7/DM_D5.md (doubled-matching lifts, D = 5), research/theorems/REGULARITIES.md (polygon covers, flag
  graphs), research/frontier/SIZE_LAW.md (Haar size law), research/structured/README.md (orbit search, haar_sym).
- Route-chart lifts: research/theorems/squad165/ (+ git show origin/claude/beat-16-5-squad-jiiwg2:research/theorems/BEAT_16_5_SQUAD.md).
