# raise-d6D10: raising the (6,10) record above 524,160

Job "raise-6-10" (Haiku worker, 2026-10-25). Record to beat: **524,160** vertices = 2N with
N = |prod sl 5 psl 7 x Z_13| = 262,080, orbit search k = 3, m = 2, f = 0 (file
research/frontier/sols/d6D10_prod_sl_5_psl_7_13_orb3f0_s1.txt; table 452,032).

## Method

Orbit-symmetric connection sets (research/structured/haar_sym, `ORBIT="3 2 0"`), as in STRUCTURE.md §8. Every
group that could beat the record is a group order N > 262,080. Their Poisson mean mu = N exp(-W/N) with
W(6,10) = 2,441,406 is about 24 to 30 there. Planning (tools/mu_plan.py): 2N = 525,032 at mu = 24, 533,003 at
mu = 28, 540,096 at mu = 32. So each unit of mu is worth about 0.4 % of vertices.

Tooling is the same as the earlier sessions: `tools/orb_screen.py 6 10 262081 276000 "3 2 0" --list` lists the
candidate orders; the screen's RANDORB tails rank them. Calibration: the record group under RANDORB (3000
samples) has min 3, p1 16, p10 37, median 281 (scratch log, not committed). The candidates at mu 24 to 25 have
min 14 to 33, p1 36 to 63. So the record group has the better tail, and the candidates need more evaluations.

## Attempts

(filled in below as runs finish)

### Batch 1 (2026-10-25 07:32–07:52, orbit k=3, m=2, f=0, K=8, 1200 s per run, one core each)

| group | N (2N) | mu | fix | result (best cost) | evals |
|---|---|---|---|---|---|
| sl 11 x Z199 | 262,680 (525,360) | 24.2 | 11 | 18 (stuck at ~6 orbits) | 5.8e6 |
| psl 13 x Z241 | 263,172 (526,344) | 24.6 | 5 | 6 | 7.2e6 |
| prod psl 5 psl 5 x Z73 | 262,800 (525,600) | 24.3 | 8 | 4 | 4.2e6 |
| psl 17 x Z109 | 266,832 (533,664) | 28.4 | 8 | 3 (one fixed point or one orbit) | 5.9e6 (still running) |

Reading: the record group solved in 7.4e4 and 2.1e5 evaluations (both at mu 23.6). None of the four μ ≈ 24–28
candidates has solved after 4–7·10⁶ evaluations. Random-S tails back this up: the record group's p1/p10 are
16/37 against 36–63 / 132–202 for these. So group quality matters more than μ here, and the fit
evals ≈ e^(μ/4.5) is too optimistic for these groups.

### Batch 2 (07:52–08:55, same settings; RESTART=1 variants, longer runs)

| group | N (2N) | mu | fix | runs | best cost | evals per run |
|---|---|---|---|---|---|---|
| prod psl 5 psl 5 x Z73 | 262,800 (525,600) | 24.3 | 8 | 3 (plain x2, RESTART x1) | 4 | 4–6e6 |
| prod psl 5 sl 5 x Z37 | 266,400 (532,800) | 27.9 | 17 | 1 | 5 | 5.8e6 |
| psl 17 x Z109 | 266,832 (533,664) | 28.4 | 8 | 7 (plain, ORBW=3, RESTART x5) | **1** in 5 runs, never 0 | 5–9e6 |
| psl 19 x Z79 | 270,180 (540,360) | 32.2 | 8 | 1 | 3 | 9.7e6 |
| psl 13 x Z247 | 269,724 (539,448) | 31.6 | 5 | 1 (stopped) | 15 | 4e6 |

Cost 1 with fixed points (ORBW=3, energy 3) means exactly one α-fixed element uncovered. psl 17 reaches this
state again and again, 5 times out of 7 runs, and never gets to 0. A single fixed point is missed with
probability about e^(-λ/3) ≈ 0.05 per random S, so this is most likely the endgame barrier, not a structural
impossibility. But it is the closest any run has come, so psl 17 gets the remaining compute.
Diagnosing which element it is would need a haar_sym change (dump the uncovered codes at cost 1); not done.

### Batch 3 (08:55–09:45): psl 17 x Z109 seeds, large-cyclic screen

- psl 17 x Z109 got about 8 more RESTART=1 runs (2000 s each, 5–10·10⁶ evals), plus one ORBW=3 run. Best cost
  is 1 in 5 runs and 3 in the others. Nothing reached 0.
- The screen of the full window with the cyclic cap raised to n ≤ 3000 (`orb_screen.py --nmax 3000`) gave new
  candidates (psl 7 × Z1561 at N = 262,248, sl 8 × Z523 at 263,592, sl 5 × Z2191, psl 9 × Z733, …). Their
  random-S minima are 156 to 40,000 against 3 for the record group, so none were run. Groups with large
  cyclic factors mix badly, as STRUCTURE.md §5 already says.

## Status and what would move it

No solution above 524,160 yet. Every μ ≈ 24–32 group tried is above the wall for this α within about 1e7
evaluations per run. Only psl 17 × Z109 approaches 0, and only in its endgame (one α-fixed element uncovered).

Next steps for a later session (not done here):
1. Make haar_sym dump the uncovered elements at cost 1 (psl 17), to see whether it is always the same fixed
   element. If it is, the α or the group is structurally blocked; if not, run many more seeds.
2. A cheaper endgame: when the cost is 1 (a fixed point), try exact moves on the fixed generators instead of
   whole orbits.
3. Route-chart or lift constructions (research/theorems/BEAT_16_5_SQUAD.md) for (6,10), which the orbit search
   does not reach at these μ.

Time spent: about 2.5 hours on 4 cores, roughly 1.5·10⁸ orbit evaluations in total.

## Final tally (stopped 2026-10-25 ~10:30)

- Logs of every run in this job: research/structured/runs/raise_d6D10/ (haar_sym RESULT lines; no solution files).
- psl 17 x Z109 (N = 266,832, 2N = 533,664 would be a new record): 14 runs, 11 of them best = 1, 3 of them best = 3,
  never 0. About 1.4·10⁸ evaluations on this group alone. All other groups: best cost 3 to 18.
- Total evaluations in this job: about 2.2·10⁸.
- No VALID graph above 524,160 was found. Nothing was added to research/frontier/sols/.
- Decision: stopped here, not because the cell is provably stuck, but because a 3-hour, 4-core search gave no
  solution and the best group sits at a fixed-point endgame. The "next steps" above are the way forward.
