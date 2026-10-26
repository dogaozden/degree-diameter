# raise-d16D9: beat 337,394,400 vertices at (Δ,D) = (16,9)

Record held: Haar graph of SL(2,151) × Z49, |G| = 168,697,200, 2|G| = 337,394,400 vertices, k=3 orbit search
(ORBIT="3 5 1", |Fix α| = 149), found in 97 evaluations at μ = 14.4 (runs/d16D9_sl_151_49_orb3_s1.log).
Table value 288,939,118. Bar to beat: |G| > 168,697,200.

## Method
- Search: research/structured/haar_sym.c (orbit search, k=3, f=1, m=5), THREADS=1, 4 runs in parallel.
- Group choice: |G| = |SL(2,p)| · n with p prime, n odd with every prime factor ≡ 1 mod 3 (rule of STRUCTURE.md §2),
  |G| just above the bar. Enumerated by a short script (candidates sorted by excess over the bar).
- Excess is cheap at first: d ln μ / d ln N ≈ 1 + W/N ≈ 17 for this cell, so +1 % in |G| costs about +17 % in μ, and
  evaluations grow like e^(μ/4.5). Climb in small steps.
- Verification: build_haar2.py for ≤ 20M vertices is not used here (all graphs > 20M). Above 20M:
  research/frontier/haarcheck_sl.c (hcsl) and research/frontier/haarcheck2.c (hc2) for SL(2,p) × Z_n, both
  independently; both binaries built from those sources in the scratchpad.

## Ladder (|G| excess over the bar)
| group | |G| | excess | status |
|---|---|---|---|
| sl 79 × Z343 | 169,085,280 | +0.23 % | running (wave 1) |
| sl 89 × Z241 | 169,876,080 | +0.70 % | running (wave 1) |
| sl 107 × Z139 | 170,266,104 | +0.93 % | running (wave 1) |
| sl 103 × Z157 | 171,541,968 | +1.69 % | queued |
| sl 79 × Z349 | 172,043,040 | +1.98 % | queued |
| sl 83 × Z301 | 172,082,904 | +2.01 % | queued |

## Log
(see bottom; newest last)

- 2026-10-25 07:44 wave 1 (haar_sym, k=3 m=5 f=1, THREADS=1, K=8): sl 79x343 solved at 1625 evals (981 s); checked
  VALID by hcsl and hc2: 338,170,560 vertices (+0.23 % over 337,394,400). Saved research/frontier/sols/d16D9_sl_79_343_orb3_s1.txt.
- 2026-10-25 ~07:55 sl 107x139 solved at 2841 evals (1190 s); VALID by hcsl and hc2: 340,532,208 vertices (+0.93 %).
  Saved research/frontier/sols/d16D9_sl_107_139_orb3_s1.txt. Checker outputs: research/frontier/runs/raise_d16D9_checks.txt.
  Current best: 340,532,208 (sl 107 x Z139).
- Running: sl 103x157 (+1.69 %, cost 2 at 1,833 evals), sl 89x241 (+0.70 %, cost 2), sl 79x349 (+1.98 %), sl 83x301 (+2.01 %).
- Notes: stdout of haar_sym is block-buffered when redirected, so logs only show RESULT at exit; solution files appear directly.
- 2026-10-25 ~08:00 sl 89x241: no solve (best 2 after 2,225 evals, 1,800 s).
- 2026-10-25 ~08:05 sl 103x157 solved at 3,617 evals (1,715 s); VALID by hcsl and hc2: 343,083,936 vertices (+1.69 %).
  Saved research/frontier/sols/d16D9_sl_103_157_orb3_s1.txt. Current best: 343,083,936.
- Running: sl 79x349, sl 83x301 (cost 12 at ~500 evals), sl 109x133 (+2.09 %), sl 137x67 (+2.12 %).
- 2026-10-25 08:05-08:21: sl 137x67 solved at 361 evals (350 s), VALID hcsl+hc2: 344,542,944 (+2.12 %). Current best.
  sl 79x349 solved at 1,569 evals (1,083 s), VALID hcsl+hc2: 344,086,080 (+1.98 %). Both saved in research/frontier/sols/.
- Running: sl 83x301 (cost 12), sl 109x133 (cost 12), sl 101x169 (+3.2 %).
- 2026-10-25 08:30: sl 101x169 solved at 1,545 evals (1,188 s), VALID hcsl+hc2: 348,207,600 (+3.19 %). Current best. Saved.
  sl 83x301: no solve (best 12, 2,201 evals).
- Running: sl 109x133 (cost 6), sl 89x247 (cost 14), sl 83x307 (+2.2 % over 101x169), sl 97x193.
- 2026-10-25 08:42: sl 109x133 solved at 3,577 evals, |G| 172,224,360 (344,448,720 vertices). Below the current best, so not checked
  and not recorded. Kept only in the scratchpad.
- Running: sl 89x247 (cost 6), sl 83x307 (cost 14), sl 97x193 (cost 18), sl 239x13 (+5.2 %).
- 2026-10-25 09:18: sl 89x247 (cost 6, 2,729 evals), sl 83x307 (cost 6, 3,809 evals), sl 97x193 (cost 12, 3,809 evals)
  timed out with no solve (2400 s each). Retrying 83x307 and 97x193 with seed 2. Still running: sl 239x13 (cost 12),
  sl 293x7 (cost 22). Best remains sl 101x169, 348,207,600.
- 2026-10-25 09:55-11:05: no solve on sl 83x307 (s2, cost 16), 97x193 (s2, s3, s4: cost 6-12), 89x247 (s2 cost 12, s3 cost 6, s4 cost 2),
  293x7 (s1 cost 12), 239x13 (s1 cost 12), 179x31 (s1, still running at last check).
- Queue: a worker script (scratchpad worker.sh, four worker lists) runs one 2400 s job per slot and verifies solves
  automatically with hcsl and hc2; results go to the scratchpad results.txt. Solve rate at 174-177M is about 1 in 4 runs
  at 2400 s, so waiting on seeds is the bottleneck.
- Best still: sl 101x169, 348,207,600 vertices (checked).

## Final state (session end, 2026-10-25 ~13:30)
- **Best verified: sl 101 x Z169, |G| = 174,103,800, 348,207,600 vertices** (+3.19 % over 337,394,400), checked by
  hcsl and hc2. File research/frontier/sols/d16D9_sl_101_169_orb3_s1.txt.
- All verified solves saved (both checkers, research/frontier/runs/raise_d16D9_checks.txt): sl 79x343 (338.2M), sl 107x139
  (340.5M), sl 103x157 (343.1M), sl 137x67 (344.5M), sl 79x349 (344.1M), sl 101x169 (348.2M). Below the best and
  not recorded: sl 109x133 (344.4M, seeds 1 and 2 in the scratchpad).
- Failed at 2400 s each (best cost in brackets): sl 89x247 [s1 6, s2 12, s3 6, s4 2], sl 83x301 [s1 12], sl 83x307
  [s1 6, s2 16, s3 14, s4 16], sl 97x193 [s1 12, s2 12, s3 8, s4 6], sl 293x7 [s1 12, s2 14, s3 10], sl 239x13 [s1 12,
  s2 4, s3 14], sl 131x79 [s1 18, s2 12], sl 79x361 [s2 32], sl 211x19 [s1 20, s2 18], sl 179x31 [s1 12, s2 16, s3 14].
- Per-run logs: the scratchpad runs/ folder (not committed). Per-rung statistics above.

## Stopping reason
The 6-hour budget is used. Next rungs (|G| above 174.1M, i.e. vertices above 348.2M) are failing at 2400 s per seed at
roughly one solve per 4-6 runs, with evaluation counts that grow with N (about 1.5k-4k evaluations per solve at
+2-3 %). A next step needs longer runs (several hours per seed) on the rungs at 174-176M (sl 89x247, sl 83x307,
sl 97x193), or Opus-level changes (a different alpha or a larger fixed set) as SIZE_LAW predicts a wall.

---

# Round 2 (branch claude/raise-d16d9-round2-ol83t8, 2026-10-25)

Starting point: round 1 left a checked candidate, **sl 101 x Z169 at 348,207,600 vertices** (sol
`research/frontier/sols/d16D9_sl_101_169_orb3_s1.txt`, checked by hcsl and hc2 in round 1). The bar for round 2 is
therefore 348,207,600, not the 337,394,400 in the round-2 brief. The coordinator should re-check that graph as well.

## Plan
- Same tool as round 1: `research/structured/haar_sym.c`, `ORBIT="3 5 1"` (k = 3, m = 5, f = 1), K = 8, THREADS = 1,
  4 jobs in parallel, 2400 s per seed. Build: `gcc -O3 -march=native -fopenmp -o haar_sym haar_sym.c -lm`;
  checkers `haarcheck_sl.c` and `haarcheck2.c` (cc -O3 -march=native).
- Groups: SL(2,p) x Z_n, p prime >= 50, n odd with every prime factor = 1 mod 3, n <= 1000, 2|G| in (348.2M, 362M].
  (sl 5/7/11 x huge Z_n are excluded: large cyclic factors mix badly, see STRUCTURE.md section 5.) Enumerated by a short
  script (27 candidates). Round 1 had already tried 89x247, 83x301, 83x307, 97x193, 293x7, 239x13, 131x79, 79x361,
  211x19, 179x31 at 2400 s; this round starts with the untried ones in that window, and uses ORBW=3 and RESTART=1 for
  some seeds.
- Verification: hcsl and hc2 for every solve (both > 20M vertices), plus haar_sym's own full diameter check.

## Round 2 log (newest last)
- 15:07 re-check of the 348.2M candidate started (hcsl, hc2).
- 15:07 wave 1 started: 27 candidates in order of vertex count, one seed each, 2400 s, four at a time.
- 15:07 348.2M candidate re-checked: hcsl VALID (vertices 348207600, ecc 9), hc2 VALID (same). Bar stays 348,207,600.
- Results at 2400 s (k=3 m=5 f=1, default settings, seed 1; cost = uncovered elements, 0 = solved):
  | group | N (vertices) | best cost | evals | note |
  |---|---|---|---|---|
  | sl 89 x Z247 | 348,210,720 | 6 | 1,329 | no solve |
  | sl 61 x Z769 | 349,002,960 | 36 | 1,161 | large cyclic factor, weak |
  | sl 71 x Z487 | 348,536,160 | 24 | 1,281 | large cyclic factor, weak |
  | sl 59 x Z853 | 350,275,920 | 42 | 1,129 | large cyclic factor, weak |
- Interrupted, no result (killed by my own process cleanup, not by the search): sl 293x7 (seed 1), sl 59x859 (seed 1), sl 83x313 (seed 1, stopped by me to keep 4 jobs on 4 cores). Re-queue later.
- Running at 16:09: sl 83x307 (seed 5, ORBW=3), sl 97x193 (seed 5, ORBW=3), sl 103x163 (seed 1), sl 139x67 (seed 1).
- Observation: evals/s is lower than round 1 (about 0.55 eval/s with four jobs at 174M, vs about 1.3 in round 1). Large cyclic factors (n > 450) are clearly weaker.
- 16:30-17:11 second batch (2400 s, seed 1 unless noted):
  | group | N (vertices) | best cost | evals |
  |---|---|---|---|
  | sl 83 x Z307 (ORBW=3, seed 5) | 351,026,256 | 30 | 1,465 |
  | sl 97 x Z193 (ORBW=3, seed 5) | 352,254,336 | 14 | 1,625 |
  | sl 103 x Z163 | 356,195,424 | 24 | 1,689 |
  | sl 139 x Z67 | 359,854,320 | 32 | 993 |
  | sl 109 x Z139 | 359,987,760 | 24 | 2,249 |
  | sl 79 x Z361 | 355,917,120 | 24 | 1,665 |
- Still running at 17:11: sl 83x313 (seed 2), sl 131x79 (seed 3), and four 10,000 s seeds on sl 89 x Z247 (seeds 2, 3, RESTART=1 seed 4, ORBW=3 seed 5), started as slots free.
- Round-2 status: 0 solves above 348,207,600 in 14 finished runs (2400 s each, one seed except the ORBW/RESTART variants). Best cost 6 (sl 89x247). Large n is clearly weaker; the 300-400 range is still at cost 14-32.

---

# Round 3 (branch claude/raise-d16d9-round3-1jt4sd, 2026-10-26)

Bar: **348,207,600** (sl 101 x Z169, `research/frontier/sols/d16D9_sl_101_169_orb3_s1.txt`, checked by hcsl and hc2 in round 2).
The 337,394,400 in the brief is superseded; the coordinator has not yet recorded 348.2M, so it should re-check it too.
Round 2's last open lead: **sl 89 x Z247 at 348,210,720** (+3,120 over the bar). Its four 10,000 s seeds were still running when
round 2 ended, and their results are not on the branch. They are the first thing re-run here.

## Facts established this round
- μ = N e^(−W/N) with N = |G| (the group order), W = W(Δ,D) fixed. So μ depends only on |G|, not on the shape: at |G| = 174.1M,
  μ = 24.6 (sl 89x247 and sl 101x169 alike). d ln μ / d ln N ≈ 17, so +1 % in |G| is about +17 % in μ.
- Effective mean μ_eff = μ/k + |Fix(α)| e^(−λ/k), λ = W/N ≈ 15.8. At 174M:
  - k = 3 (3 5 1): μ/3 = 8.2, |Fix| = 89..101, misses ≈ 1.0. Needs every prime of n ≡ 1 mod 3.
  - k = 4 (4 4 0, f = 0): μ/4 = 6.2, |Fix| = 87..99, misses ≈ 3.4..3.9. The tool picks α = conj(order 4 in SL, i.e. an
    involution of PSL) × (z → r z) with r of order 4 mod n. So n needs one prime ≡ 1 mod 4; the other primes take r = −1.
    This opens groups with small n (e.g. sl 157 x Z45, sl 191 x Z25), which k = 3 cannot use at this size.
  - k = 5 (5 3 1): needs every prime of n ≡ 1 mod 5; the candidates above the bar all have larger n.
- Round 2 found large cyclic factors (n > 450) weak for k = 3. The k = 4 family is the one untried family with small n.
- Screen (5 s, 9 evals): sl 101x169 k=4 start cost 7.7M (degenerate start, not informative); sl 89x247 k=4 start 124.
  Short screens do not separate shapes; comparisons need 2400 s runs.

## Round 3 log (newest last)
- 01:3x screen (5 s, one seed each): sl 89x247 k=3 μ 24.62, |Fix| 89; sl 101x169 k=3 μ 24.61, |Fix| 101; k=4 f=0 on both.
- 01:4x wave 1: sl 89x247 k=3 seeds 11 (10,000 s) and 12 (RESTART=1, 10,000 s); sl 157x45 k=4 f=0 seed 1 (2,400 s); sl 191x25 k=4 f=0 seed 1 (2,400 s).
  Two k=4 runs on sl 89x247 were started then stopped (they test the large-n group again; not useful).
- Results go to scratchpad results.txt; verified solves go to research/frontier/sols/.
- 02:20 k=4 f=0 wave 1 (2,400 s, seed 1, four-slot): sl 191 x Z25 best 132,574,040; sl 157 x Z45 best 287,389,760.
  Both stayed at the start cost for the whole run (1,993 evals each). A cost near 0.76 N or 1.6 N means the BFS
  reaches only part of the graph: S with f = 0 falls in a set that does not generate a connected Haar graph here.
  **k = 4 with f = 0 is dropped** (no fix tried). f = 4 with three fixed generators would give d = 16 but is the
  weak f ≥ 3 case of STRUCTURE §8, not tried.
- 02:10 wave 2 (10,000 s each): sl 89 x Z247 k=3 seed 13 (RESTART=1) and seed 14 (ORBW=3), joining seeds 11 and 12.
  Four 10,000 s runs on sl 89 x Z247 are now going, which is the only lead at the bar (348,210,720).
- 04:26 sl 89 x Z247 k=3 seeds 11 and 12 (10,000 s each): best cost 6 both (6,137 and 6,185 evals). No solve. Seed 12 used
  RESTART=1. Seeds 13 (RESTART=1) and 14 (ORBW=3) were still running at cost 12 at 7,000 s.
- 04:26 new: sl 83 x Z307 (351.0M, RESTART=1, seed 21, 10,000 s) and sl 97 x Z193 (352.3M, RESTART=1, seed 22, 10,000 s).
