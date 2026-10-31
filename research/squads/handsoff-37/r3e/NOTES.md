# r3e NOTES (Haiku worker r3e, squad handsoff-37, card r3e: breakout weights on the far-46 basin at n = 170, no symmetry)

Start: 2026-10-31 19:35:56 UTC (date -u). Stop by 21:15Z (final notes then).

Plan: own engine r3e/brk.c (unsymmetric 2-switch tabu with breakout weights on far pairs, focused moves: pick a far pair
(x,y), candidates = 2-switches with one edge near x and one edge near y). Start from the far-46 graph (r3e/start170_far46.edges),
the c2 far-70 graph (r3e/start170_c2_far70.edges), and C168.1 + random switches (calibration at n = 168).

## 19:36-19:56 engine and first results (n = 170, far-46 basin; calibration n = 168)

Code: r3e/brk.c (build: gcc -O3 -march=native -o brk brk.c; usage ./brk START.edges SEED SECS TAG [PERT]; env FULL=1
full neighbourhood of all valid 2-switches, FR1/FR2 focus radius (FULL=0), TEN tabu tenure (4), WCAP weight cap (16), VW=1
vertex weights instead of pair weights, WIN=weights file, BOWALK=1). Cost = weighted far, weights start at 1 and grow by 1 on
every far pair at a local minimum of the weighted cost; real far (score37 definition) tracked separately. Verified: the
far value after applying the chosen move equals the predicted far (CHK=1 prints both; the only mismatch was a debug bug, fixed).
seg.sh TAG SEED SECS START chains a run from out/TAG_cur.edges and out/TAG_w.txt (weights).

Speed: full neighbourhood of a cubic graph at n = 170 has about 30,900 2-switches; one far evaluation is about 8 us
(bit-parallel radius-7 reach, 3 words), so one FULL step takes about 0.18 s (5.5 steps/s). Focused neighbourhoods are much
smaller but useless here (see below).

- Focused candidates (FR1 = 1, FR2 = 1: all 2-switches with one edge within distance 1 of each endpoint of a far pair, 81
  candidates): the best candidate from the far-46 graph has far 111 (every candidate increases far). FR = 2: best far 67. FR1 = 3,
  FR2 = 2: best far 66. So no improving move lies near one far pair; the full neighbourhood is needed.
- Full breakout (FULL=1) from the far-46 graph, pair weights, WCAP 16, TEN 4: 281 steps (80 s): best 46, walk 48-58. Chained
  segments fb46 (3 x 95 s, weights saved): best 46 only (the walk stays between 46 and 62).
- Vertex weights (VW=1, WCAP 16, 90 s): walk 46-53, best 46.
- WCAP 200 (90 s, 324 steps): walk 58-69, best 46.
- Start c2/best170 (far 70): best 68 after 2 steps, then the walk drifts up to 170-190 (weights 1 on new far pairs make the
  weighted cost prefer moves that fix bumped pairs and open new ones; cost drifts up, not down).
- Start r3c n170_C5_far65 (far 65): best 65, walk drifts to 200 in 90 s (same drift).
- Calibration n = 168: C168.1 + 20 random 2-switches (far 871), FULL breakout 90 s (321 steps): best far 123 (no far 0).
  For comparison c1 plain tabu from C168.1 stalls at 123-163. So breakout is not clearly stronger in this budget.

## 19:56-20:31 more runs (all n = 170 unless said; far values are score37 far)

- Far-46 start, chained full breakout (fb46, WCAP 16, TEN 4), 9 segments of 95 s (about 2,600 steps in total, weights saved
  and restored): best 46 again and again; the walk stays between 46 and 62. No far < 46.
- TEN = 10 (tabu tenure): walk drifts to 178-216 (too long a tabu forces the walk away). Keep TEN = 4.
- WCAP 4 / 16 / 200: walk 46-69 in every case; no change in the far-46 basin.
- PAWS-style decay (every 20 bumps weights drop by 1): calibration n = 168 from C168.1 + 20 switches: best 133 (vs 116-123
  without decay). Not used.
- Sampled candidates (3000 random 2-switches per step, 31 steps/s): walk drifts to 187-234 (missed improving moves look like
  local minima, so bumps happen far too often). Full neighbourhood is needed.
- Far-46 start with 10 random 2-switches first (new basin): best 138 in 90 s. The far-46 basin is a strong attractor.
- Escape test from C168.1 (far 0): with 2, 4 or 6 random 2-switches the search returns to far 0 in 2-10 steps (trivially, by
  undoing the switches). With 10 switches it stalls at far 125 (45 s, 147 steps). With 20 switches: 116-127 (90 s and chained
  segments). So the 2-switch basin of C168.1 is narrow, and breakout does not climb back from 10+ switches.
- All far pairs of the far-46 graph are SAME-SIDE pairs at distance exactly 8 (46 pairs, 76 vertices involved, at most 2 per
  vertex). The far-70 graph (c2): 70 same-side pairs at distance 8, 90 vertices, at most 5 per vertex. No cross-side far pairs.
- Start c2/best170 (far 70) with pair weights and BASEW = 4 (pair cost 4 + W - 1 instead of W, so breakout weights matter
  less): best 61 after 4 s (logged: r3e/best/n170_c2brk_far61.edges). Then the walk drifts to 164-175.
- Reset-to-best (RESET = 15, reload the best graph when real far > best + 15, weights kept) from the far-61 graph: best 59
  (logged: r3e/best/n170_c2r_far59.edges, far 59, diam 8, score37 checked). Later segments from the far-59 graph: best 59
  (c2s runs: 59-65). No further improvement.
- Breakout from the r3c C5 far-65 graph (90 s): best 65, walk drifts to 200. Vertex weights (VW=1) from far 46: 46-53.

## Summary (stop 21:15 UTC, see final section)
