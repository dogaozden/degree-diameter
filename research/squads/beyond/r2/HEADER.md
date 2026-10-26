# Squad "beyond", round 2: shared header (read this first, then your card)

Job new-cells-beyond (Opus director, 2026-10-26, branch claude/new-cells-beyond-etos3t). Goal: the FIRST values for 48
cells outside the 2013 bipartite degree-diameter table: Δ = 17..20 at D = 3..10, and D = 11, 12 at Δ = 3..10.
A value = a bipartite graph of maximum degree ≤ Δ and diameter ≤ D that we built and checked. Repo root:
/home/user/degree-diameter (all paths below are relative to it).

## Machine rules (4 cores, 15 GB, shared by ~18 cards and the director)
- Single thread (THREADS=1, no OpenMP threads > 1). Every heavy command: `timeout 900 nice -n 10 <cmd>`.
- Memory ≤ 1.5 GB per process unless your card says otherwise. Never start more than one heavy process at a time.
- No git commands that change anything (no add/commit/checkout/stash). Reading other branches is fine:
  `git show origin/<branch>:<path>`.
- Write only inside your card folder research/squads/beyond/r2/<card>/ (create it). Build binaries there.
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
Append to research/squads/beyond/r2/scoreboard.jsonl:
`{"card": "c07", "cell": "18,5", "idea": "<one line>", "code": "<path>", "command": "<exact command that rebuilds the graph>",
"score": <vertices>, "valid": true|false, "check": "<path of the checker output you saved>", "next": "<one line>"}`
Save every valid graph you claim as `research/squads/beyond/r2/<card>/<cell>_n<vertices>.edges.gz` (gzip of the apsp
input) or, if too big to save, the exact builder command. Reply to the director in at most 5 lines.

## Already found / already ruled out (do not redo; round-1 work is in research/squads/beyond/r1/<card>/)
Current best checked values (all verified by the director):
- D=3: 546 / 614 / 624 / 762 (Δ=17..20; 17, 18, 20 are Moore graphs). D=4: 8,738 / 10,440 / 10,982 / 14,480.
- D=5: (17,5) 33,792 (only the (16,5) route-chart lift; round 1 found nothing larger); (18,5) **47,600** = the
  multi-doubled-matching lift of W(13) (research/frontier/beyond/MDM.md: Z2 × Z(2k+1), k doubled matchings, needs only a
  parity condition (A) on W(q)); (19,5) 52,428 expected from DM on W(16) (card r1/c05, still running) and 52,360 polygon
  cover 11·|W(13)|; (20,5) **75,000** = route-chart lift over F5 (r1/c04: chart with 22 singular patterns, K3,3 +
  doubled matching over Z20, m = 60; Z22 stalled at cost 4 on one seed).
- D=8: (17,8) 41,373,072 (Haar SL(2,53)×Z139, r1/c15); (18..20,8) the director's Haar queue is running.
- D=11/12: (3,11) 1,008 (Haar PSL(2,7)×Z3), (3,12) 1,320 (Haar PSL(2,11)), (4,11) 17,600 and (4,12) 48,000
  (metacyclic Haar, r1/c13), (5,11) 158,928, (5,12) 229,824, (6,11) 659,568 (r1/c14; the director is rerunning these
  with research/bighaar/haar_big.c), (7,11) 10.6M, (7,12) 56.3M, (8,11) 43.7M, (8,12) 268.5M, (9,12) 1.06B, (10,12) 3.5B
  (director). The director runs all Haar searches at D ≥ 8 with Δ ≥ 5 and at D = 9, 10, 11, 12: cards do not.
- Ruled out in round 1: blind annealing of Z8 / Z10 voltage lifts of W(13) with extra matchings (r1/c06, r1/c07: cost
  stays in the thousands); building flag graphs for Δ ≤ 20 at every D (r1/c16: nothing above the values above; D = 5
  capped at 31,460); random Haar / double covers at (18,7) (r1/c17); MDM with odd extra degree (a plain matching adds no
  sheet); MDM at D = 7 over H(q) (counting).
- Also ruled out before: see research/squads/beyond/r1/HEADER.md.

## Theorem docs (read only what your card needs)
- research/theorems/POLISHED.md is on branch origin/claude/thm-polish-2oddll (fourth hat §2, Theorems A/B/C §3–5,
  Theorem D/R §6–7, Haar lemma §8): `git show origin/claude/thm-polish-2oddll:research/theorems/POLISHED.md`.
- research/theorems/D7_HEXAGON.md on origin/claude/d7-hexagon-theorems-4w1prt (level graphs, hubs at D = 7).
- research/d10D7/DM_D5.md (doubled-matching lifts, D = 5), research/theorems/REGULARITIES.md (polygon covers, flag
  graphs), research/frontier/SIZE_LAW.md (Haar size law), research/structured/README.md (orbit search, haar_sym).
- Route-chart lifts: research/theorems/squad165/ (+ git show origin/claude/beat-16-5-squad-jiiwg2:research/theorems/BEAT_16_5_SQUAD.md).
