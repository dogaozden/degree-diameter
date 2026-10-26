# Cell (Δ, D) = (8, 7): raise our record above 43,344

Job "raise-8-7" (Haiku worker, 2026-10-25). Record to beat: **43,344** vertices = 2·|SL(2,8) × Z_43| (N = 21,672),
Haar graph, k = 3 orbit search, ORBIT "3 2 2" (`../../structured/STRUCTURE.md` §4, file
`../../frontier/sols/d8D7_sl_8_43_orb3_s1.txt`). Table value 40,586.

## Why the window is narrow

A Haar graph on G has 2N vertices, N = |G|. The first-moment wall μ = N·exp(−W/N) with W = 137,257 for (8,7)
grows with N, so only groups with N in [21,673, ~22,100] have μ ≲ 43. Above that μ ≥ 45 and the orbit search has
not solved anything at (8,7) (pgl 9 × Z31, μ 47.6: best cost 9 after 8.7·10⁶ evaluations).

Candidates with N in [21,673, 22,500] from `../../structured/tools/orb_screen.py 8 7 21673 26000 "3 2 2" --anyn`
(random-S minimum cost over 300 samples; the record group has min 17 at μ 38.5):

| group | N | 2N | μ | fix | random min |
|---|---|---|---|---|---|
| pgl 5 × Z181 | 21,720 | 43,440 | 39.1 | 5 | 84 |
| sl 5 × Z181 | 21,720 | 43,440 | 39.1 | 5 | 180 |
| prod psl 3 × psl 3 × Z151 | 21,744 | 43,488 | 39.4 | 8 | 1036 |
| sl 7 × Z65, pgl 7 × Z65 | 21,840 | 43,680 | 40.7 | 29 | 69–70 |
| psl 9 × Z61 | 21,960 | 43,920 | 42.4 | 8 | 59 |
| psl 17 × Z9 | 22,032 | 44,064 | 43.4 | 26 | 29 |
| pgl 4/sl 4/psl 5 × Z367 | 22,020 | 44,040 | 43.2 | 2 | 414+ (poor) |
| pgl 9 × Z31, sl 9 × Z31 | 22,320 | 44,640 | 47.6 | 8–17 | 36, 46 |

Other (k, m, f) values for d = 8: k = 2 (m = 4, f = 0 or m = 3, f = 2), k = 4 (m = 2, f = 0), k = 5 (m = 1, f = 3). These
screened worse on the same windows (random min ≥ 40 on the best ones).

## Runs

- Calibration (120 s, one thread, ORBIT "3 2 2", seed 1, ~6·10⁶ evals each): pgl 7×65 best 6, pgl 9×31 best 9, psl 17×9
  best 10, psl 9×61 best 12. None solved.
- Wave 1 (3600 s each, seed 11, logs in the scratchpad): psl 17×9, pgl 7×65, psl 9×61, pgl 5×181.

- Wave 1 result (3600 s each, seed 11, ~1.6–2.3·10⁸ evals each): psl 17×9 best 3, pgl 7×65 best 6, psl 9×61 best 12,
  pgl 5×181 best 24. None solved.
- Wave 2 (3600 s each): psl 17×9 with ORBW=3 (seed 12), psl 17×9 with RESTART=1 (seed 13), pgl 7×65 with ORBW=3
  (seed 12), psl 17×9 plain (seed 14).

- Wave 2 result (3600 s each): psl 17×9 best 3 in all three variants (ORBW=3 seed 12, RESTART=1 seed 13, plain seed 14),
  about 1.6·10⁸ evals each. pgl 7×65 with ORBW=3 best 9 (worse than plain's 6). None solved. The cost-3 floor on
  psl 17×9 is the same across seeds and variants, which suggests no orbit-symmetric solution for this α, not a slow search.
- Wave 3 (3600 s each): sl 7×65 (seed 21), pgl 9×31 (seed 21), sl 9×31 (seed 21), psl 9×61 with RESTART=1 (seed 22).

- Wave 3 result (3600 s each): pgl 9×31 best 6 (seed 21), sl 9×31 best 6 (seed 21), sl 7×65 best 6 (seed 21),
  psl 9×61 with RESTART=1 best 12 (seed 22). None solved. About 2.2·10⁸ evals each.

## Status: stopped, nothing above 43,344

Three waves (about 12 one-hour runs, roughly 2.5·10⁹ evaluations on 4 cores) over every candidate group with
N in [21,673, 22,500] and the k = 3, m = 2, f = 2 orbit structure. Best costs: 3 (psl 17×9, three variants and seeds),
6 (pgl 9×31, sl 9×31, sl 7×65, pgl 7×65 plain), 12 (psl 9×61), 24 (pgl 5×181). Nothing solved.

Why stopped: the cost floors are the same across seeds and variants, the group windows are exhausted, and BEYOND_RANDOM
§1.5 already puts (8,7) near the orbit-space ceiling. Not proven: each orbit space is still far larger than the
evaluations spent, so a much longer run on psl 17×9 (cost 3) or pgl 9×31 (cost 6) remains the cheapest next step.

Not tried: k = 2, 4, 5 structures on these groups beyond the random-S screen; Lean/lift routes.

# Round 2 (job raise2-8-7): resumed from round 1

Starting point: round 1 stopped at 43,344 after orbit search (k = 3, ORBIT "3 2 2") on the Q × Z_n groups in
[21,673, 22,500] (sl/psl/pgl/prod families only, from `tools/orb_screen.py`). Round 2 tried routes round 1 listed as
untried, and one family round 1 never screened.

## Routes and results so far

1. **Voltage lifts over 2+2 and 3+3 bases** (`research/lifts/lift.c`, Haar-dipole check first). Degree-8 bases from
   `enum_bases.py` (2+2: 4 bases; 3+3: 37). Target orders N = 10,840 (2+2, n = 43,360) and N = 7,230 (3+3, n = 43,380).
   Calibration, 150 s each, one thread: 2+2 meta 10×1084 ⋊ 9 best 1,368 (at 60 s), 2+2 meta 20×542 ⋊ 11 best 1,734,
   2+2 meta 5×2168 ⋊ 4 best 276 (30 s), 3+3 meta 15×482 ⋊ 4 best 630. The cost counts pairs over k sources, so these
   are 70–340 per source. A Haar (dipole) anneal on meta 571 ⋊ 38 (N = 21,698) reached 41 over 2 sources in 120 s.
   **Negative for now:** the lifts anneal far worse than Haar at this order in this budget. Not pursued further.
2. **SL(2,8) × Z_n family at N in the window:** only n = 43 is in range (504·43 = 21,672). SL(2,8) × Z_44 (22,176) has no
   order-3 automorphism on Z_44, so the orbit search falls back to conjugation only (random min 1,532). Dead end.
3. **Metacyclic groups in orbit mode (not screened in round 1).** `tools/orb_screen.py` enumerates only SL/PSL/PGL and
   products, so metacyclic Z_m ⋊_r Z_k was never orbit-screened. Enumerated all meta specs with N in [21,673, 22,500]
   and every prime of m ≡ 1 (mod 3) (so the scaling (a,j) ↦ (ua,j), u of order 3, has u − 1 a unit):
   3,827 specs (383 orders). `meta_specs.txt`, `meta_orb322_screen.txt` (RANDORB 300 each, ORBIT "3 2 2").
   Best random minima: meta 3109 ⋊_1652 7 (N = 21,763, μ 39.7, |Fix| 6): min 12, median 432; meta 3109 ⋊_2511 7: min 30;
   meta 1843 ⋊_501 12 (N = 22,116): min 32; meta 1591 ⋊_371 14 (N = 22,274): min 32.
   Anneals, 1,200 s each, one thread, ORBIT "3 2 2" (`haar_sym 8 7 1200 SEED 8 OUT meta m k r 1`):
   3109⋊1652 floor 12 (reached within 30 s, then flat); 3109⋊2511 floor 12 (same); 1843⋊501 best 39; 1591⋊371 best 44.
   The floors are reached in seconds and never move, so the cost is structural for these α (fixed-point misses), not a
   slow search. None solved.

3b. **Second tier and status.** Tier 1 (44 specs, min ≤ 60, 60 s each) and tier 2 (160 specs, min 61–150, 45 s each):
   best floors 12 (3109 family), 14, 18 (2413⋊9 1119; 991⋊22 at 20), then 24 and up. Floors are reached in seconds and
   stay flat; the random-screen minimum is only a weak predictor (967⋊23 had min 46 and floor 14). Logs and
   specs: `raise2-d8D7/sweeps/`. Solutions: none (no `.sol` files written).

## Status: stopped, nothing above 43,344

Round 2 covered: (a) metacyclic groups in the window under ORBIT "3 2 2" (all 3,827 specs screened; 204 annealed, 60 s
to 1,200 s each); (b) lifts over 2+2 and 3+3 degree-8 bases at the target orders (calibrated, far behind Haar); (c) the SL(2,8)
family (only n = 43 is in range, and it is the record). Best costs: 12 (meta 3109⋊7, 20 min flat), 14, 18.

Why stopped: the floors are structural (reached in seconds, unchanged for 20 min, consistent across two seeds
and two r-values of the same group). With the same α, longer runs do not move them. What remains untested:
other α structures on metacyclic groups (k = 2, 4, 5 with m and f as in round 1), 3+3 lifts at larger N, and
groups with a prime factor ≡ 2 (mod 3) in m (which raises |Fix(α)|). Each of these is a separate program; I did
not judge any of them likely enough for a Haiku run to be worth it.

# Round 3 (job raise3-8-7): resumed from round 2 (branch claude/raise2-8-7-haar-p4jkz1)

Record to beat: **43,344** (sl 8 × Z_43, N = 21,672, ORBIT "3 2 2"). Targets must have N ≥ 21,673.

## Method: count cost-0 hits by random sampling, not only anneal floors

Round 2 judged the k = 3 floors (3–12) as structural. Round 3 measured the zero rate directly with
`ORBIT="3 2 2" RANDORB=n haar_sym 8 7 1 1 8 <out> <group>`. Each sample is a random valid S of the orbit form
(about 40 µs each, one core, with the full diameter check and file writing on any cost 0 hit):

- record group sl 8 × Z_43, 200,000 samples: **3 zero-cost hits** (rate ≈ 1.5·10⁻⁵), first at sample 19,054. It passes
  the full diameter check (`haar_sym` writes it; see below). Calibration for the rest of this round.
- (Round 2's 300-sample minimum of 17 on the same group was simply too few samples.)

## Routes tried in round 3

1. **ORBIT "7 1 1" (one free orbit of 7, f = 1) on sl 8 × Z_43, the record group.** The orbit space has only ~3,100
   orbits, and random sampling over 60,000 covers it. Best cost 32. Dead.
2. **ORBIT "7 1 1" screen, N in [21,673, 30,000]** (`orb_screen.py ... --samples 20000`). Best cost 94 (sl 7 × Z_71,
   μ 75.7), then 114 (sl 29), 162 (pgl 7 × Z_71). The groups with no order-7 element in Q give degenerate results (α is
   trivial on Q). Dead.
3. **ORBIT "5 1 3" (one free orbit of 5 plus two α-fixed generators, f = 3) on groups with primes of n ≡ 1 (mod 5)**,
   N ≥ 21,673. One million random samples per group (≈ 1.6·10⁵ distinct (fixed-pair, orbit) combinations, so
   essentially exhaustive): sl 9 × Z_31 **min 10**; prod psl 3 × sl 4 × Z_31 **min 10** (N 22,320); psl 9 × Z_61 min 140;
   sl 5 × Z_181 min 200. None reaches 0. Dead, and the best-exhausted k = 5 value (10) is what the k = 5 wall predicts.
4. **ORBIT "3 2 2" random minima at 20,000 samples** (for comparison): sl 8 × Z_43 min 0 (the record); sl 9 × Z_31 min 6;
   pgl 9 × Z_31 min 12; prod psl 3 × sl 4 × Z_31 min 10; psl 17 × Z_9 min 10 (N = 22,032, 2N = 44,064).
   Next step (below): long random scans of these four groups for zero hits.
