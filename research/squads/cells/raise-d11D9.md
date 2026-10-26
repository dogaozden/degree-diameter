# Cell (Δ,D) = (11,9): raise the record above 16,792,080

Job "raise-11-9" (Haiku worker, branch claude/raise-d11d9-record-2x1d57). Goal: a Haar graph H(G,S) with
|G| > 8,396,040 (2|G| > 16,792,080), 11-regular, diameter 9, verified.

## Current record and why it is where it is

- Record: sl 61 × Z_37 (|G| = 8,396,040), orbit k = 3, m = 3, f = 2, μ = 15.0, solved after 4,969 evaluations
  (`research/structured/runs/d11D9_sl_61_37_orb3_s1.log`, `research/frontier/sols/d11D9_sl_61_37_orb3_s1.txt`).
- μ = N e^(−W/N), W = 111,111,111 for (11,9). μ ladder (largest |G| with μ ≤ m):
  μ 15 → 8.395M, μ 20 → 8.568M, μ 25 → 8.707M, μ 30 → 8.824M, μ 35 → 8.925M, μ 40 → 9.015M.
  So each unit of μ buys about 0.1–0.2 % in |G| near here; the gains come from running at higher μ.
- Evaluation cost: sl 61 × Z37 (wide rows) ≈ 0.05 s/eval; sl 31 × Z283 (no cyclic subgroup of order ≥ 64, haar_gen3
  evaluation) ≈ 0.023 s/eval, single thread.
- Earlier attempts at this cell in research/structured/runs: psl 257 × Z1 stalled at cost 73 (involutions, odd D);
  sl 107 × Z7 stalled at cost 2 after 40k evals; psl 61 × Z73 solved but is smaller (8,282,580).

## Rules of thumb used

- SL-type groups only (no PSL factor): odd D has involution misses with PSL (see research/structured/STRUCTURE.md §2.6).
  Char-2/3 groups kept out except SL(2,4), SL(2,8) factors (few involutions).
- n has all prime factors ≡ 1 (mod 3).
- ORBIT="3 3 2" (d = 2 + 3·3 = 11), K = 8, THREADS = 1, nice.

## Driver

`scratchpad` (not in repo): `job.sh SECS SEED GROUP...` runs `haar_sym 11 9 SECS SEED 8 out GROUP`, then checks any
solution with two independent low-memory checkers (`research/frontier/haarcheck_sl.c`, `haarcheck2.c`); prod
groups need `build_haar2.py` instead.

## Log

- 2026-10-25 wave 1 (1200 s, seed 1, 4 at a time): 18 SL-only candidates from μ 15.3 to 30.2. Results in the table below.

## Result 1: NEW RECORD (11,9), 16,853,760 vertices (was 16,792,080, +0.36 %)

- Group prod sl 7 × sl 11 × Z_19, |G| = 8,426,880, orbit k = 3, m = 3, f = 2, μ = 15.8. Solved at evaluation 11,545 (wave 1, seed 1, 281 s).
- Solution: research/frontier/sols/d11D9_prod_sl_7_sl_11_19_orb3_s1.txt. Search log: research/structured/runs/d11D9_prod_sl_7_sl_11_19_orb3_s1.log.
- Independent check: build_haar2.py (rebuild from definitions): ecc 9 from (e,A) and (e,B), 0 unreached, VALID d=11 D=9,
  edge list sha256 280a20185193497c49a74d56b8e89929c74a8ca632540b58c6b7c398d9305de3. Log: runs/d11D9_prod_sl_7_sl_11_19_orb3_s1.rebuild.txt.
- The SL checkers (haarcheck_sl / haarcheck2) do not read prod headers; build_haar2 is the checker for prod groups.

## Result 2: NEW RECORD (11,9), 17,108,208 vertices (was 16,853,760, +1.5 %)

- Group sl 37 × Z_169, |G| = 8,554,104 (μ = 19.5), orbit k = 3, m = 3, f = 2, solved at evaluation 28,417 (499 s, seed 1).
  Z_169 = Z_13², and 13 ≡ 1 (mod 3), so the n-condition holds.
- Solution: research/frontier/sols/d11D9_sl_37_169_orb3_s1.txt. Search log: research/structured/runs/d11D9_sl_37_169_orb3_s1.log.
- Independent checks: haarcheck_sl and haarcheck2 both VALID (eccA = eccB = 9, 17,108,208 vertices). build_haar2.py VALID:
  ecc 9 from both sides, 0 unreached, edge-list sha256 d01a1283c41fc441de811a629ee4222acb9443db44a9ac2e47ae2f2da5c6befb.
  Log: runs/d11D9_sl_37_169_orb3_s1.rebuild.txt.

## Result 3: NEW RECORD (11,9), 17,169,600 vertices (was 17,108,208, +0.36 %)

- Group sl 49 × Z_73 (SL(2,49) over GF(7)[x]/(x²+1), |G| = 8,584,800), μ = 20.5, orbit k = 3, m = 3, f = 2, solved at evaluation 31,033 (826 s, seed 1).
- Solution: research/frontier/sols/d11D9_sl_49_73_orb3_s1.txt. Search log: research/structured/runs/d11D9_sl_49_73_orb3_s1.log.
- Independent check: build_haar2.py VALID: ecc 9 from both sides, 0 unreached, edge-list sha256 0aea5ec6ee8e0dd9547da7514883b8364b6338fba88f6b53a912b4ab123921b2.
  Log: runs/d11D9_sl_49_73_orb3_s1.rebuild.txt. The prime-only SL checkers do not handle GF(49), so build_haar2 is the checker here.

## Wave 1 results (seed 1, 1200 s unless noted; ORBIT="3 3 2", K = 8, THREADS = 1)

| group | |G| | μ | result |
|---|---|---|---|
| prod sl 7 × sl 11 × Z19 | 8,426,880 | 15.8 | **solved** (11,545 evals), record 1 |
| sl 37 × Z169 | 8,554,104 | 19.5 | **solved** (28,417 evals), record 2 |
| sl 49 × Z73 | 8,584,800 | 20.5 | **solved** (31,033 evals), record 3 |
| sl 31 × Z283 | 8,422,080 | 15.7 | best 12 (47k evals) |
| prod sl 5 × sl 8 × Z139 | 8,406,720 | 15.3 | best 6 (24k) |
| sl 29 × Z349 | 8,501,640 | 17.9 | best 12 (45k) |
| prod sl 3 × sl 37 × Z7 | 8,503,488 | 18.0 | best 4 (39k) |
| prod sl 5 × sl 7 × Z211 | 8,507,520 | 18.1 | best 32 (43k) |
| prod sl 3 × sl 13 × Z163 | 8,543,808 | 19.2 | best 24 (25k) |
| prod sl 3 × sl 17 × Z73 | 8,577,792 | 20.3 | best 8 (31k, 1136 s) |
| prod sl 3 × sl 11 × Z271 | 8,585,280 | 20.6 | best 48 (20k) |
| prod sl 3 × sl 71 × Z1 | 8,588,160 | 20.7 | best 12 (32k) |
| sl 43 × Z109 | 8,661,576 | 23.3 | best 12 (47k) |
| sl 41 × Z127 | 8,747,760 | 26.6 | best 10 (49k) |
| prod sl 5 × sl 7 × Z217 | 8,749,440 | 26.7 | best 38 (55k) |
| sl 29 × Z361 | 8,793,960 | 28.6 | best 30 (55k) |
| sl 59 × Z43 | 8,828,760 | 30.2 | best 8 (37k) |
| sl 107 × Z7 | 8,574,552 | 20.2 | best 2 (stopped by hand after 81 s, 2.7k evals, to free a slot) |

Notes: the three solutions came at evaluations 11k–31k, with μ 15.8–20.5. Of the 18 wave-1 runs, 3 solved; the other
15 stopped at best cost 2–48 within 1200 s, with many at 8–12. That is one seed per group, so it says little about
the solve rate per group. Cost 12 recurred on several groups; a plateau there is not established.

## Wave 2 (seed 2, 2400 s, started 09:11): in progress
prod sl 3 × sl 71, prod sl 4 × sl 11 × Z109, prod sl 3 × sl 11 × Z271, sl 43 × Z109 (seed 2), then sl 41 × Z127,
prod sl 5 × sl 7 × Z217, sl 29 × Z361, sl 59 × Z43 (seed 2) and prod sl 8 × sl 11 × Z13.

---

# Round 2 (branch claude/raise-d11d9-record-round2-k45ls9, started 2026-10-25 14:20 UTC)

Job "raise2-11-9". The brief's 16,792,080 is stale: round 1 (branch claude/raise-d11d9-record-2x1d57) verified three
records, the best 17,169,600 (sl 49 × Z73, |G| = 8,584,800, build_haar2 VALID, two low-memory checkers not applicable
to GF(49)). Round 2 therefore has to beat **17,169,600**, i.e. find |G| > 8,584,800 (N_h = 2|G| > 17,169,600). Round 1's
README/records table still shows 16,792,080 (the coordinator has not moved it yet).

Round 1 left wave 2 "in progress" with no result lines committed, so its wave-2 outcome is unknown. Treat its wave-2
groups as not run.

## Method for round 2

- Only SL-type groups (odd D, PSL factors have involutions, STRUCTURE §2.6). Candidates from
  `research/structured/tools/orb_screen.py 11 9 8584801 8900000 "3 3 2" --list`, lowest μ first.
- Eval cost measured (BENCH, 20 s each, THREADS=1): prod sl 3×sl 11×Z271 ≈ 0.04 s; prod sl 4×sl 11×Z109 ≈ 0.025 s;
  prod sl 8×sl 11×Z13 ≈ 0.017 s; sl 43×Z109 ≈ 0.015 s.
- Driver: scratchpad `job.sh TAG SECS SEED GROUP... n` (haar_sym 11 9, ORBIT "3 3 2", K 8, THREADS 1, nice).
  Not in the repo; the command is the same as in the round-1 logs.
- Wave 2a (started 14:26, 7200 s each): prod sl 3×sl 11×Z271 (μ 20.6, seed 1), prod sl 8×sl 11×Z13 (μ 22.8, seed 1),
  sl 43×Z109 (μ 23.3, seed 2), prod sl 4×sl 11×Z109 (μ 22.2, seed 1).

## Results

(none yet)

### Wave 2a progress (14:58 UTC, ~31 min in, 7200 s budget each, no solution yet)

| group | |G| | μ | evals | best cost |
|---|---|---|---|---|
| prod sl 3 × sl 11 × Z271 | 8,585,280 | 20.6 | 45k | 48 |
| prod sl 4 × sl 11 × Z109 | 8,632,800 | 22.2 | 78k | 6 |
| prod sl 8 × sl 11 × Z13 | 8,648,640 | 22.8 | 109k | 2 |
| sl 43 × Z109 (seed 2) | 8,661,576 | 23.3 | 123k | 6 |

## Result 4 (round 2): NEW RECORD (11,9), 17,297,280 vertices (was 17,169,600, +0.75 %)

- Group prod sl 8 × sl 11 × Z_13 (SL(2,8) with x³+x+1, SL(2,11), Z_13), |G| = 8,648,640 (μ = 22.8), orbit k = 3,
  m = 3, f = 2. Solved at evaluation 109,745 (1884 s, seed 1, wave 2a). |Fix(α)| = 107.
- Solution: research/frontier/sols/d11D9_prod_sl_8_sl_11_13_orb3_s1.txt. Search log: research/structured/runs/d11D9_prod_sl_8_sl_11_13_orb3_s1.log.
- Independent check: build_haar2.py VALID: ecc 9 from (e,A) and (e,B), 0 unreached, 11-regular, 0 duplicate edges,
  edge-list sha256 a51d7f96174920381a935a1b0b7b2fd22e285c23672c8cd28716c787f8eaf9a8. Log: runs/d11D9_prod_sl_8_sl_11_13_orb3_s1.rebuild.txt.
- Wave 2a's other runs were still going at 14:59 (see the progress table above).

### Wave 2b (15:04 UTC): bar raised to 17,297,280 (|G| > 8,648,640)

- prod sl 3 × sl 11 × Z271 (8,585,280) and prod sl 4 × sl 11 × Z109 (8,632,800) were stopped: both are below the new bar.
  Their last progress: best 48 (46k evals) and 6 (79k evals); not solved.
- Still running (started 15:04 unless noted, 7200 s each):
  - sl 43 × Z109 (seed 2, μ 23.3, from 14:26, best 6 at 125k evals at 14:59)
  - sl 41 × Z127 (seed 2, μ 26.6)
  - prod sl 3 × sl 11 × Z277 (seed 1, μ 27.8)
  - prod sl 5 × sl 7 × Z217 (seed 1, μ 26.7)

### Wave 2b results (16:29 UTC)

- sl 43 × Z109 (seed 2, μ 23.3): full 7200 s, not solved. Best 2 at 477k evals (one uncovered orbit or two fixed points).
- prod sl 3 × sl 11 × Z277 (μ 27.8): stopped at 118k evals, best 78 (poor; not a candidate).
- Running now (started 15:04–16:28, 7200 s each): sl 41 × Z127 (seed 2, best 8 at 366k at 16:27), prod sl 5 × sl 7 × Z217 (seed 1, best 36 at 404k),
  prod sl 4 × sl 13 × Z67 (seed 1, μ 28.0, N 8,779,680), prod sl 9 × sl 23 × Z1 (seed 1, μ 26.5, N 8,743,680; no cyclic factor).

### Wave 2c results (17:02 UTC)

- sl 41 × Z127 (seed 2, μ 26.6): full 7200 s, not solved. Best 8 at 513k evals (fixed points, |Fix| = 41).
- prod sl 5 × sl 7 × Z217 (seed 1, μ 26.7): full 7200 s, not solved. Best 36 at 567k evals.
- Still running: prod sl 4 × sl 13 × Z67 (μ 28.0, best 12 at 76k at 16:55) and prod sl 9 × sl 23 × Z1 (μ 26.5, best 14 at 126k at 16:55).
- Started 17:02 with ORBW=3 (an uncovered α-fixed element weighs 3; the stalls at cost 2–8 look like fixed-point misses):
  sl 43 × Z109 (seed 3, 8000 s) and sl 59 × Z43 (μ 30.2, seed 1, 8000 s).
- Budget: session 6 h from 14:20 UTC; stop new launches by ~19:30 and finish verification before the end.

### Wave 2c results (18:28 UTC)

- prod sl 4 × sl 13 × Z67 (μ 28.0): full 7200 s, not solved. Best 6 at 267k evals.
- prod sl 9 × sl 23 × Z1 (μ 26.5): full 7200 s, not solved. Best 14 at 452k evals (|Fix| = 431: a big fixed-point set, as expected without a cyclic factor).
- Still running, ORBW=3: sl 43 × Z109 (seed 3) and sl 59 × Z43 (seed 1), both at best 6 at 5200 s, ending about 19:15 UTC.
- No new launches: the remaining time is too short for a 2-hour run at these μ.

## Result 5 (round 2): NEW RECORD (11,9), 17,323,152 vertices (was 17,297,280, +0.15 %)

- Group sl 43 × Z_109 (SL(2,43) × Z_109), |G| = 8,661,576 (μ = 23.3), orbit k = 3, m = 3, f = 2, **ORBW=3**
  (an uncovered α-fixed element weighs 3). Solved at evaluation 433,953 (6522 s, seed 3). |Fix(α)| = 41.
  The same group with ORBW=1 (seed 2, 7200 s, 477k evals) stalled at cost 2: the ORBW=3 change is what closed it.
- Solution: research/frontier/sols/d11D9_sl_43_109_orbw3_s3.txt. Search log: research/structured/runs/d11D9_sl_43_109_orbw3_s3.log.
- Independent check: build_haar2.py VALID: ecc 9 from (e,A) and (e,B), 0 unreached, 11-regular, 0 duplicate edges,
  edge-list sha256 459b3467e7b17e228a9f11fedd05fa6a51e4fb16258756aaab1833d691ce352b. Log: runs/d11D9_sl_43_109_orbw3_s3.rebuild.txt.
- Caveat: one success is not a measured advantage for ORBW=3 (STRUCTURE §8 says the same about (11,8)); the second
  ORBW=3 run (sl 59 × Z43, μ 30.2) was still running at this commit.

### Final status (19:15 UTC, round 2)

- sl 59 × Z43 (ORBW=3, seed 1, μ 30.2): full 8000 s, not solved. Best 6 at 465k evals (|Fix| = 59).
- No background runs left. Round 2 ends with the record at **17,323,152** (sl 43 × Z109), above round 1's 17,169,600.
- Best open leads for a next round: (a) more ORBW=3 seeds on sl 43 × Z109-like groups at μ 23–26 (sl 43 solved at 434k evals with ORBW=3,
  so the cost-2/6 stalls on sl 41 × Z127 (μ 26.6, best 8) and prod sl 4 × sl 13 × Z67 (μ 28.0, best 6) are the next thing to retry with ORBW=3);
  (b) sl 59 × Z43 (μ 30.2) and prod sl 4 × sl 13 × Z67 need more than 8000 s; (c) prod sl 9 × sl 23 × Z1 (μ 26.5) stalled at 14 with |Fix| = 431: a
  cyclic factor (or k = 5) is probably needed there.
- Not tried in round 2: the faster orbit evaluation (STRUCTURE §7.4), k = 5 at this order, and groups with n in 2 or more primes ≡ 1 (mod 3).

---

# Round 3 (branch claude/d11d9-record-round3-ffo51a, started 2026-10-26 01:19 box time)

Job "raise3-11-9". The brief's 16,792,080 is stale and so is the records table on master (it still shows 16,792,080):
round 2 verified **17,323,152** (sl 43 × Z109, |G| = 8,661,576, ORBW=3, build_haar2 VALID). The bar for round 3 is
therefore **|G| > 8,661,576** (2|G| > 17,323,152). The round-2 branch is merged into this branch, so its solution file
(research/frontier/sols/d11D9_sl_43_109_orbw3_s3.txt) and LOG lines are here.

## Candidates above the bar (orb_screen --list, window 8,661,577 … 8,900,000, k = 3, m = 3, f = 2)

Odd D: PSL(2,q) has ~q²/2 involutions, which costs misses (STRUCTURE §2.6). So the candidates are SL-type, or
products where the small factor is A4 = PSL(2,3) (12 elements, 3 involutions) times SL(2,q), which has few involutions.
Lowest μ among these:

| group | |G| | μ | round-2 status |
|---|---|---|---|
| prod psl 3 × sl 13 × Z331 (A4 × SL(2,13)) | 8,674,848 | 23.7 | not tried |
| prod psl 3 × sl 47 × Z7 (A4 × SL(2,47)) | 8,717,184 | 25.4 | not tried |
| sl 41 × Z127 | 8,747,760 | 26.6 | ORBW=1: best 8 (513k evals) |
| prod sl 4 × sl 13 × Z67 | 8,779,680 | 28.0 | ORBW=1: best 6 (267k evals) |
| sl 59 × Z43 | 8,828,760 | 30.2 | ORBW=3: best 6 (465k evals) |

Not repeated: prod sl 5 × sl 7 × Z217 (best 36), prod sl 9 × sl 23 × Z1 (best 14, |Fix| 431), prod sl 3 × sl 11 × Z277
(best 78), sl 29 × Z361 (best 30 in round 1).

## Wave 1 (ORBW=3, seed 1, 7200 s each, THREADS=1, 4 at a time; queue files in scratchpad, outputs in runs/r3/)

- started 01:19 (box time): the four rows above, all with `ORBIT="3 3 2" ORBW=3 K=8`.

### Wave 1 result (03:19 box time, 7200 s each, all four stopped unsolved)

| group | |G| | μ | best cost | evals | |Fix| |
|---|---|---|---|---|---|
| sl 41 × Z127 | 8,747,760 | 26.6 | 6 | 353k | 41 |
| prod psl 3 × sl 47 × Z7 (A4 × SL(2,47)) | 8,717,184 | 25.4 | 6 | 148k | 143 |
| prod sl 4 × sl 13 × Z67 | 8,779,680 | 28.0 | 6 | 189k | 35 |
| prod psl 3 × sl 13 × Z331 (A4 × SL(2,13)) | 8,674,848 | 23.7 | 48 | 156k | 35 |

The A4 × SL(2,13) run stuck at 48 (a large plateau), so it is dropped. The other three sit at cost 6, which
is one or two uncovered orbits or fixed points.

### Wave 2 (ORBW=3, seeds 2 and 3, 8000 s each, started 03:20 box time, ends about 05:35)

- sl 41 × Z127, seeds 2 and 3.
- prod psl 3 × sl 47 × Z7, seeds 2 and 3.

## Result 1 (round 3): NEW RECORD (11,9), 17,495,520 vertices (was 17,323,152, +1.0 %)

- Group sl 41 × Z_127 (SL(2,41) × Z_127), |G| = 8,747,760 (μ = 26.6), orbit k = 3, m = 3, f = 2, **ORBW=3**, seed 3.
  Solved at evaluation 30,937 (725 s, wave 2). |Fix(α)| = 41. Seed 1 (wave 1, 7200 s, 353k evals) stalled at cost 6.
- Solution: research/frontier/sols/d11D9_sl_41_127_orbw3_s3.txt. Search log: research/structured/runs/d11D9_sl_41_127_orbw3_s3.log.
- Independent checks, all VALID, ecc 9 from both sides, 0 unreached, 11-regular:
  - haarcheck_sl (research/frontier/haarcheck_sl.c): n = 17,495,520.
  - haarcheck2 (research/frontier/haarcheck2.c): n = 17,495,520, eccA = eccB = 9.
  - Output: research/structured/runs/d11D9_sl_41_127_orbw3_s3.rebuild.txt.
  - build_haar2.py: running in the background. Its output goes to research/structured/runs/d11D9_sl_41_127_orbw3_s3.build_haar2.txt.
- Note on the earlier wave-2 runs: sl 41 × Z127 seed 2 and A4 × SL(2,47) × Z7 seeds 2 and 3 were stopped at 03:35.
  Their order is below the new bar (|G| > 8,747,760), so they could not raise the record.

## Wave 3 (ORBW=3, 7200 s each, started 03:35 box time, ends about 05:50)

Bar: |G| > 8,747,760 (2|G| > 17,495,520). The orders above it with usable structure:
- prod sl 4 × sl 13 × Z67 (μ 28.0): seeds 2 and 3. Wave 1, seed 1: best 6 at 189k evals.
- prod sl 5 × sl 7 × Z217 (μ 26.7, N 8,749,440): seed 1. Earlier (ORBW=1): best 36 at 567k evals.
- sl 29 × Z361 (μ 28.6, N 8,793,960): seed 1. Earlier (ORBW=1): best 30 at 55k evals.

### Wave 3 status (04:37 box time, about 80 min in)

- prod sl 4 × sl 13 × Z67, seeds 2 and 3: best 12 and 6 (93k and 92k evals). Still running, end about 05:50.
- prod sl 5 × sl 7 × Z217 (seed 1): stopped at 04:37, best 50 after 187k evals. Not promising.
- sl 29 × Z361 (seed 1): stopped at 04:37, best 30 after 185k evals. Not promising.
- Replaced by sl 59 × Z43 (μ 30.2, N 8,828,760), ORBW=3, seeds 1 and 2, 6000 s each, started 04:36, end about 06:17.
  Wave 1 of the earlier round: best 6 at 465k evals on this group, so it is the most promising remaining order above the bar.

### Wave 3 result (05:35 box time)

- prod sl 4 × sl 13 × Z67, seed 2: not solved, best 3 after 191k evals (closest of this round after the record).
- prod sl 4 × sl 13 × Z67, seed 3: not solved, best 6 after 187k evals.
- Two more seeds on the same group were started at 05:36 (seeds 4 and 5, 4000 s each, end about 06:43).
