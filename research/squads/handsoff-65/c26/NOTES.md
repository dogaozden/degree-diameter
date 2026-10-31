# c26 notes (card: "1,6|1,6"-type coset graphs with NON-CYCLIC hub stabilisers, orders 294..312)

## Model (same block structure as c18, N = 5,1,1,0)
G acts by right multiplication. A0 = G, A1 = G/H, B0 = G, B1 = G/K, |H| = |K| = 6, H and K any subgroups of order 6
(C6 or S3). n = 7|G|/3 (686 for |G| = 294). Blocks: S = 5 elements (A0-B0: x ~ s^-1 x), g01 (A0-B1: x ~ coset K(g01^-1 x),
one edge), g10 (A1-B0: coset Hx ~ inv(h g10) x for h in H, six edges); no A1-B1 block. Degrees are checked in build().
Diameter: the four representatives (A0 identity, A1 coset of 1, B0 identity, B1 coset of 1) must reach everything in 5
steps; cost = sum over the 4 representatives of far vertices (the same scale as c18's t18 and mcos).

## Tools
- subs.g: GAP, lists all subgroups of order 6 of SmallGroup(ORDER,i) with type C6/S3, indexed like c18/groups tables.
  Output in c26/subs/sub6_ORDER_i.txt (e.g. `gap -q -c 'ORDER:=294; OUTDIR:="subs";' subs.g`).
- t26.c (gcc -O3 -march=native -o t26 t26.c -lm): tabu over S, g01, g10, H, K (full neighbourhood, bitmask all-pairs
  propagation for the 4 representatives, about 21 us per evaluation). Usage:
  `t26 TABLE SUBS HT KT SEED TLIM TENURE OUT` with HT, KT in {C6, S3}; env HIDX/KIDX fix start, FIXHK=1 freezes H, K.
  Writes OUT (edge list) at every new best; stops at cost 0 and prints CLAIM.
- Groups: c18/groups/sg_ORDER_i.txt tables (c18 generated them).

## Results
- Calibration (cyclic, c18's 294_11, C6 C6): seed 8, 240 s -> cost 5 (c18's t18 reached 2 in 144 s with its own moves).
- S3|S3 screen, 50 s each, seed 1, tenure 12:
  294_3 166, 294_5 176, 294_20 200, 294_21 69, 294_22 158, 294_7 13 (294_7 = (C7xC7):S3, 49 S3 subgroups).
  294_3, 294_5, 294_20, 294_21, 294_22 have few or structurally bad S3 hubs at this budget.

## Status 20:19 UTC
- Speed: 21 us per evaluation (bit-parallel propagation of the four representatives), about 45 tabu steps per second.
- Screen, 14 s per combo, seed 1, tenure 12 (run/screen.tsv; combos from `subs/sub6_*` with S3 subgroups, mixed S3|C6
  and C6|S3 where both types exist; screen.sh TLIM SEED COMBOFILE, combo lists run/chunk_00..05):
  300_22 S3|S3 28, 300_26 S3|C6 38, 300_26 C6|S3 39, 300_26 S3|S3 39, 300_25 50-53, 306_8 S3|S3 60, 300_37 84;
  294_7 not in the screen (50 s: 13). Most 306/312 combos 90-200 at 14 s.
- Deep runs (230 s):
  294_7 S3|S3 seed 2 (tenure 12): cost 10, check.sh bad = 1470, file run/s3_294_7_s2.edges (scoreboard line written 20:10).
  300_22 S3|S3 seed 2 (tenure 12): cost 21 (n = 700), file run/deep_300_22_s2.edges.

## Status 20:40 UTC: 294_7 (S3|S3) runs, 230 s each, check.sh bad (far pairs) in brackets
- seed 2, tenure 12: cost 10 [bad 1470]; seed 5, tenure 20: cost 8 [bad 1176]; seed 6, tenure 30: cost 9;
  seed 7, tenure 20: cost 7 [bad 1029] (best so far, run/s3_294_7_s7.edges; the 285 s rerun is identical and stalls at 7
  from step 4381); seed 9, tenure 20: cost 10.
- Scoreboard personal best for c26: n = 686, bad = 1029 (294_7, S3|S3, seed 7).
- Observation: the best S3-hub states have H = S3 with K = S3 and cost 7-10; no cost-0 found at 686 or 700.
- Not done (time): an INIT option to restart tabu from the best state, C6|S3 mixing on 294 (no group of order 294 has
  both types), screen of 306/312 combos beyond chunk_02 (14 s results 60 and above).

## Status 20:58 UTC (final list of runs, 230 s unless noted)
- 294_7 S3|S3: seeds 2/5/6/7/9/11/13/15 (tenure 12-30) cost 10, 8, 9, 7, 10, 10, 9, 10; seed 17 (180 s) cost 9.
  Best: seed 7, tenure 20, cost 7, check.sh bad = 1029 (run/s3_294_7_s7.edges). Scoreboard line written.
- 300_22 (C5 x A5, n = 700) S3|S3: seed 2 cost 21, seed 5 tenure 20 cost 14 (bad 1600, run/deep_300_22_s5.edges).
- Calibration with cyclic C6 hubs on c18's 294_11: cost 5 at 240 s (t18 of c18 reached 2); t26 is about 2x weaker here.
- Result: no cost-0 graph at 686 or 700. Next ideas: INIT restart from the cost-7 state, a tabu that moves the
  double-coset structure (1,1 blocks), a finer cost (far pairs weighted by orbit size), and screen the 306/312 S3 combos
  longer (14 s screen gave 60+).
- seed 19 (150 s): cost 10; seed 21 (170 s): see run/deep_294_7_s21.log. No cost 0 found.
