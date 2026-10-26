# Squad "beyond", round 1: shared header (read this first, then your card)

Job new-cells-beyond (Opus director, 2026-10-26, branch claude/new-cells-beyond-etos3t). Goal: the FIRST values for 48
cells outside the 2013 bipartite degree-diameter table: Δ = 17..20 at D = 3..10, and D = 11, 12 at Δ = 3..10.
A value = a bipartite graph of maximum degree ≤ Δ and diameter ≤ D that we built and checked. Repo root:
/home/user/degree-diameter (all paths below are relative to it).

## Machine rules (4 cores, 15 GB, shared by ~18 cards and the director)
- Single thread (THREADS=1, no OpenMP threads > 1). Every heavy command: `timeout 900 nice -n 10 <cmd>`.
- Memory ≤ 1.5 GB per process unless your card says otherwise. Never start more than one heavy process at a time.
- No git commands that change anything (no add/commit/checkout/stash). Reading other branches is fine:
  `git show origin/<branch>:<path>`.
- Write only inside your card folder research/squads/beyond/r1/<card>/ (create it). Build binaries there.
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
Append to research/squads/beyond/r1/scoreboard.jsonl:
`{"card": "c07", "cell": "18,5", "idea": "<one line>", "code": "<path>", "command": "<exact command that rebuilds the graph>",
"score": <vertices>, "valid": true|false, "check": "<path of the checker output you saved>", "next": "<one line>"}`
Save every valid graph you claim as `research/squads/beyond/r1/<card>/<cell>_n<vertices>.edges.gz` (gzip of the apsp
input) or, if too big to save, the exact builder command. Reply to the director in at most 5 lines.

## Already found / already ruled out (do not redo)
- Moore graphs (optimal, classical): (17|18|20, 3) = 546 / 614 / 762 (PG(2,q)); (17|18|20, 4) = 8,738 / 10,440 /
  14,480 (W(q)); (17|18|20, 6) = 2,236,962 / 3,017,196 / 5,227,320 (H(q)). Cards c01, c02, c08 build and check them.
- Formula values the director already has (cards build/check them, others must beat them): (19,3) 624 fourth hat q=17;
  (19,4) 10,982 Theorem A q=17; (19,6) 3,203,968 Theorem D q=17 m=2; D=5: polygon covers (2j+1)·|W(q)| at Δ=q+1+j
  (any matchings, proved): (17,5) 33,320, (18,5) 42,840, (19,5) 52,360, (20,5) 61,880 (all q=13); doubled matching
  6·|W(q)| at Δ=q+3 (annealed, research/d10D7/DM_D5.md): (19,5) 52,428 (q=16), (20,5) 62,640 (q=17).
  D=7: polygon covers (2r+1)·|H(q)| at Δ=q+1+r: (17,7) 5,631,276 (q=13,r=3), (18,7) 7,240,212 (q=13,r=4),
  (19,7) 11,184,810 (q=16,r=2), (20,7) 15,658,734 (q=16,r=3).
- Floors (monotonicity n_b(Δ,D) ≥ n_b(Δ−1,D), n_b(Δ,D−1)): (17,5) ≥ 33,792 (our (16,5) route-chart lift),
  (17,8) ≥ 36,201,060 (table (16,8)), (17,9) ≥ 337,394,400, (17,10) ≥ 4,708,566,360; (Δ,11) ≥ our (Δ,10):
  800, 12,416, 95,472, 524,160, 2,237,760, 7,818,096, 23,975,280, 60,141,120 for Δ = 3..10.
- The director runs the big Haar searches: D = 9, 10 at Δ = 17..20 and D = 11, 12 at Δ = 7..10
  (research/bighaar/haar_big.c, now with odd D). Cards: do not run Haar searches in those cells.
- Ruled out before (other sessions): random-S Haar graphs at D = 5..7 for Δ ≥ 17 (size law: far below the covers);
  regular flag graphs of buildings for Δ ∈ 17..20 (degrees are (q+1)^k); three parallel matching copies over Z9 on W(q)
  (Δ = q+4) at q ≤ 11 (counting, DM_D5.md); 3-regular route-chart controllers (perfect only to m = 12); voltage lifts of
  the A4 flag graph (unique walks); plain Z_k lifts of W(q) at D = 5 with Δ = q+1.

## Theorem docs (read only what your card needs)
- research/theorems/POLISHED.md is on branch origin/claude/thm-polish-2oddll (fourth hat §2, Theorems A/B/C §3–5,
  Theorem D/R §6–7, Haar lemma §8): `git show origin/claude/thm-polish-2oddll:research/theorems/POLISHED.md`.
- research/theorems/D7_HEXAGON.md on origin/claude/d7-hexagon-theorems-4w1prt (level graphs, hubs at D = 7).
- research/d10D7/DM_D5.md (doubled-matching lifts, D = 5), research/theorems/REGULARITIES.md (polygon covers, flag
  graphs), research/frontier/SIZE_LAW.md (Haar size law), research/structured/README.md (orbit search, haar_sym).
- Route-chart lifts: research/theorems/squad165/ (+ git show origin/claude/beat-16-5-squad-jiiwg2:research/theorems/BEAT_16_5_SQUAD.md).
