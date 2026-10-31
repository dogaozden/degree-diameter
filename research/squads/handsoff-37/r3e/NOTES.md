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
