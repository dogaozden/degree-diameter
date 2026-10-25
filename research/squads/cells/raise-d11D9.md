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
