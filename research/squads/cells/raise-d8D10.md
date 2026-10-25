# raise-d8D10: beat 7,818,096 vertices at (Δ, D) = (8, 10)

Job "raise-8-10" (Haiku worker, branch claude/raise-d8d10-record-v7wv2z, 2026-10-25).

## Starting point
- Record held: 7,818,096 vertices = 2·|SL(2,67) × Z_13| (N = 3,909,048), file
  research/frontier/sols/d8D10_sl_67_13_orb3_s12.txt (Opus squad, claude/degree-diameter-table-squad-0xgp3g).
  Table value (DS14v2 / wiki): 6,927,210. Moore bound 94,158,416.
- Re-verified in this session: research/structured/tools/hcsl (independent low-memory SL checker): VALID, ecc 10 from both sides.
- Re-found in this session: `haar_sym 8 10 60 1 8 ... sl 67 13` with ORBIT="3 2 2" solves the record order in 57 s
  (20,929 evaluations, μ ≈ 23). So the orbit ladder is reproducible and cheap at μ ≈ 23.

## Method
- research/structured/haar_sym, ORBIT="3 2 2" (k = 3 orbit-symmetric generator set, f = 2 fixed letters, m = 2 orbits;
  Δ = 2 + 3·2 = 8). Runs by tools/orbq.sh (bash tools/orbq.sh JOBS OUTDIR haar_sym). Not executable: call with bash.
- Build: `gcc -O3 -march=native -fopenmp -o haar_sym haar_sym.c -lm` in research/structured (done here).
- Checkers built here: tools/hcsl (SL), tools/hc2 (SL, second), tools/haarcheck_psl (PSL) from research/frontier and
  research/structured/tools. build_haar2.py is the reference for ≤ 20M vertices.
- Speed: ≈ 350 evaluations/s per process at N ≈ 4·10^6 (2.9 ms each).
- Target orders (tools/orb_screen.py 8 10 3909048 4400000 "3 2 2" --list): SL/PSL/PGL(2,q)×Z_n and products with
  μ = N e^(−W/N), W = 47,079,208. μ ≈ 23 at the record; μ = 31 at N ≈ 4.0M (+2.4 %); μ = 40 at N ≈ 4.08M (+4.4 %).

## Runs (4 cores, each queue one process)
| queue | group | N | μ | budget | state |
|---|---|---|---|---|---|
| A | sl 27 × Z199 | 3,911,544 | 23.2 | 1200 s (+1800 s) | running (started 07:27 UTC) |
| B | sl 37 × Z79 | 3,998,664 | 30.8 | 3600 s | running |
| C | sl 83 × Z7 | 4,001,928 | 31.1 | 3600 s | running |
| D | sl 29 × Z163 | 3,970,680 | 28.2 | 1800 s | running |
Logs: research/structured/runs/raise-d8D10/{A,B,C,D}/*.log, queue logs in runs/raise-d8D10/*.queue.log.

60-second benchmark (4 parallel, seed 1, ORBIT 3 2 2): sl 67×Z13 solved (20.9k evals); sl 83×Z7 best 6, sl 37×Z79 best 9,
psl 49×Z67 best 6 (all after ~19–23k evals).

## Results
(none yet)

## Progress log
- 07:43 UTC (≈ 930 s in): no solve yet. Best cost / evals: C sl 83×Z7 (N 4,001,928, μ 31.1) cost 1 at 2.8e5 evals;
  A sl 27×Z199 (3,911,544, μ 23.2) cost 3 at 3.1e5; B sl 37×Z79 (3,998,664, μ 30.8) cost 3 at 3.6e5; D sl 29×Z163
  (3,970,680, μ 28.2) cost 9 at 2.4e5.

## RECORD 1: sl 37 × Z79, 7,997,328 vertices (+2.3 % over 7,818,096)
- File: research/frontier/sols/d8D10_sl_37_79_orb3_s1.txt (sha256 e2dea96188f6d95b852a4d8cd90f8207eeb0447456baccf4f3ae44e6b0f890fe).
  Log: research/structured/runs/raise-d8D10/B/d8D10_sl_37_79_orb3_s1.log. ORBIT="3 2 2", μ = 30.8, 586,777 evaluations, 1,533 s.
- Checks: haar_sym full diameter check OK; orbq queue's build_haar2.py: VALID (ecc 10 both sides, 7,997,328 vertices);
  tools/hcsl: VALID; tools/hc2: VALID.
- The ladder is working above μ ≈ 30: each solve took 2–25 min, so the next rung is N > 3,998,664.
- 08:27 UTC: sl 83×Z7 seed 1 (N 4,001,928, μ 31.1) ended at 3,600 s, best cost 1, 1.09e6 evals, no solve.
  Also no solve yet: sl 83×Z7 seed 2 (best 3), pgl 83×Z7 (best 2), prod psl 9 × psl 9 × Z31 (best 6); sl 23×Z331 stopped at 25.
  Started sl 83×Z7 seed 3 (K queue). Products with a large cyclic factor (prod sl 5 sl 7 199, prod psl 5 sl 8 133) mix badly.
  The 2 sub-record runs (sl 27×Z199, sl 29×Z163) stopped: both below the record.

## RECORD 2: sl 83 × Z7, 8,003,856 vertices (+0.05 % over 7,997,328; +2.4 % over 7,818,096 of the Opus squad)
- File: research/frontier/sols/d8D10_sl_83_7_orb3_s3.txt (sha256 57ec279aebb28d56e8a124c4e66889efd97ec238392e4fb83f01f754eaaaec22).
  Log: research/structured/runs/raise-d8D10/K/d8D10_sl_83_7_orb3_s3.log. ORBIT="3 2 2", μ = 31.1, 352,729 evaluations, 1,177 s.
- Checks: haar_sym full diameter check OK; orbq's build_haar2.py VALID (ecc 10 both sides, 8,003,856 vertices);
  tools/hcsl VALID; tools/hc2 VALID (ecc 10 both sides).
- Stopped as sub-record: sl 83×Z7 seed 2 (best 3 at 1e6 evals) and pgl 83×Z7 (best 2 at 4.5e5), same order, no gain.
- Running now (N must exceed 4,001,928): prod psl 9×psl 9×Z31 (4,017,600, best 6), prod psl 5×sl 7×Z199 (4,011,840),
  psl 29×Z331 (4,031,580). Logs under runs/raise-d8D10/{J,L,M}.
- prod psl 9×psl 9×Z31 (4,017,600): ended at 3,600 s, best 6, no solve. psl 29×Z331 (4,031,580): best 21, stopped.
  prod psl 5×sl 7×Z199 (4,011,840): best 15, stopped. Large cyclic factors (Z199, Z331) do badly here.
- Running (N must exceed 4,001,928): psl 43×Z103 (4,092,396, μ 41, 3 h budget), sl 25×Z259 (4,040,400, μ 35),
  prod psl 5×sl 13×Z31 (4,062,240, μ 38, seeds 1 and 2).
- Candidates checked by hand above 4,001,928 with k = 3 valid cyclic factors (all primes ≡ 1 mod 3): SL/PSL/PGL(2,q)×Z_n
  for n in {31, 37, 43, 61, 79, 103, 109, 133, 139, 259, 331}; the order window is tight, so few are left at μ ≤ 40.
- 10:10 UTC: prod psl 5×sl 13×Z31 seed 1 (N 4,062,240, μ 38): 3,600 s, best 3, 7.2e5 evals, no solve.
  psl 43×Z103 (N 4,092,396, μ 41): seeds 1 and 2 at best 3 and 9 after about 1e6 and 6e5 evals; seed 3 started (3 h).
  prod psl 5×sl 13×Z31 seed 2 at best 6. sl 25×Z259 stopped at 18.
- Record still 8,003,856 (sl 83×Z7). The plateau at cost 3 (one uncovered orbit) appears at μ ≈ 38–41.
  Resume: research/structured/tools/orbq.sh with queue files in runs/raise-d8D10/q (bash, not exec).

## Final status (12:05 UTC)
- Best verified record: 8,003,856 vertices, sl 83 × Z7 (research/frontier/sols/d8D10_sl_83_7_orb3_s3.txt).
  Prior record at the start of the job: 7,818,096. Gain +2.4 %.
- After the record, the orbit ladders above 4,001,928 (μ 35–41) all stopped at cost ≥ 3 (one uncovered orbit):
  psl 43×Z103 seed 1 reached 3.1e6 evaluations at cost 3; seeds 2 and 3 at 6–13 after 2.1–2.7e6. prod psl 5×sl 13×Z31
  (2 seeds, 3.6e3 s each) at 3 and 6. psl 29×Z331 (21), prod psl 5×sl 7×Z199 (15), prod psl 9×psl 9×Z31 (6),
  sl 25×Z259 (18) all stopped early. Runs were stopped at 12:05 UTC; none is still running.
- Judgment: the method's wall for this cell is near μ ≈ 38–41 with these groups. The next rung needs more
  compute than the 6-hour budget gave, or a new group family (SL(3,q) or a different α, as STRUCTURE.md §7 suggests).

---

# Round 2 (job raise2-8-10, branch claude/raise2-8-10-record-dmm6z4, 2026-10-25)

## Bar
- Current record: **8,003,856 vertices** (sl 83 × Z7, N = 4,001,928, research/frontier/sols/d8D10_sl_83_7_orb3_s3.txt).
  The round-2 brief's 7,818,096 is the old Opus record, superseded by round 1. Re-checked here: research/frontier/haarcheck_sl.c
  → VALID, 8-regular, ecc 10 from both sides, N = 4,001,928.
- Round 1 left the ladder at μ ≈ 38–41 with cost-3 plateaus (orbit k = 3, f = 2). Its groups are in its notes; not repeated here.

## What round 1 did not try (and why it is the lead here)
- Round 1 only tried groups with a cyclic factor Z_n (n = 7, 13, 79, 103, 259, 331, 31, ...). Its notes say big cyclic
  factors mix badly, and every group with N > 4,001,928 and μ ≤ 35 except one was already in its ladder.
- **Products of two nonabelian groups with no cyclic factor** (n = 1) were never run. In the window (N = 4,001,929–4,200,000,
  tools/orb_screen.py … --list) the only one with μ ≤ 33 is `prod psl 11 psl 23 1`: N = 4,007,520, μ = 31.7, |Fix(α)| = 71.
  Smoke test: α = conjugation by a pair of order-3 elements (both factors move), 260 evaluations/s, no degenerate fixed set.

## Round 2, batch 1: prod psl 11 × psl 23 (n = 1), N = 4,007,520, μ 31.7, k = 3, f = 2, 4 runs × 3000 s
| run | setting | best | evals | result |
|---|---|---|---|---|
| s1 | plain | 3 | 7.5e5 | no solve |
| s2 | plain | 3 | 7.5e5 | no solve |
| s3 | RESTART=1 | 6 | 7.5e5 | no solve |
| s4 | ORBW=5 | 3 | 7.4e5 | no solve |
Logs: research/structured/runs/raise2-d8D10/p11_23_s{1..4}.log. Cost 3 = one uncovered orbit plateau, the same wall as round 1
at μ ≈ 38–41. Round 1's sl 83 × Z7 (μ 31.1) solved in 3.5e5 evaluations, so this group mixes worse than the cyclic one at equal μ.
Note: the group has |Fix(α)| = 71 and α is found by haar_sym's random search (index 3907387).

## Round 2, batch 2 (started; 5400 s each, 4 cores)
- prod psl 7 × psl 19 × Z7 (N 4,021,920, μ 33.2), seeds 1, 2.
- prod psl 3 × psl 25 × Z43 (N 4,024,800, μ 33.5), seed 1.
- prod psl 3 × sl 19 × Z49 (N 4,021,920, μ 33.2), seed 1.

### Batch 2 interim (stopped early)
- prod psl 3 × psl 25 × Z43 (seed 1): best 9 after 2.4e5 evals. Stopped at 2,000 s.
- prod psl 3 × sl 19 × Z49 (seed 1): best 11 after 2.7e5 evals. Stopped at 2,000 s.
- prod psl 7 × psl 19 × Z7 (seeds 1, 2): cost 3 plateau at 4e5 evals, same wall as batch 1. Running to 5,400 s.

## Round 2, batch 3: k = 7 (new route; round 1 used k = 3 only)
Reason: with k = 3 and Δ = 8 the two fixed letters (f = 2) must lie in C(α), an abelian torus, so they commute and their words
collide. That is the probable source of the cost-3 wall at μ 31–33 in every group tried. k = 7 gives Δ = 1 + 7 (f = 1: only e),
so no commuting fixed pair. The price is |Fix(α)|·e^(−λ/7) fixed-point misses, so the group must have a small centralizer of α.
- Screen (tools/orb_screen.py … "7 1 1" --list) lists many groups where α cannot exist (7 ∤ |Q|). Filtered to 7 | |Q|:
  - prod psl 7 × sl 7 × Z71 (N 4,007,808, μ 31.7): smoke test |Fix| = 97, expected misses ≈ 18. Rejected.
  - psl 13 × Z3683 (N 4,021,836, μ 33.2): |Fix| = 6, expected misses ≈ 1.3. Best candidate. Cyclic factor is big (29 · 127), so
    mixing is the risk. 40-second smoke test: cost 1996, far from the k = 3 starts, so a long run is needed to judge.
  - pgl/sl 13 × Z1849 (N 4,038,216 family), psl 13 × Z3697 (N 4,037,124): same idea, not run yet.
- Runs: psl 13 × Z3683, k = 7, f = 1, seeds 1 and 2, 5,400 s each.

### Batch 3 result: k = 7 is dead for Δ = 8 (stopped after 630 s on both seeds)
- psl 13 × Z3683 (|Fix| = 6, expected misses 1.3): cost stuck at exactly 1996 for 1.8e5 evaluations, both seeds. A constant
  cost means the moves change nothing: a single α-orbit of 7 generators (m = 1 is forced when Δ = 1 + 7) gives a generating
  set whose words collide structurally. The k = 7 route needs Δ = 1 + 7m, so Δ = 8 is the only option, and it fails.
  Other k = 7 candidates in the window (sl/pgl 13 × Z1849, psl 13 × Z3697, psl 7 × sl 7 × Z71 with |Fix| = 97) share the same
  m = 1 form or the fixed-point problem. Not pursued.

## Batch 4 (running): more seeds on the two best k = 3 product groups
- prod psl 11 × psl 23 (N 4,007,520, μ 31.7): seed 5 with ORBW=5, seed 6 plain; 5,400 s each.
- prod psl 7 × psl 19 × Z7 (N 4,021,920, μ 33.2): seeds 1, 2 from batch 2, still at cost 3 at 2,700 s; running to 5,400 s.

## RECORD CANDIDATE 2: prod psl 7 × psl 19 × Z7, 8,043,840 vertices (+0.5 % over 8,003,856)
- File: research/frontier/sols/d8D10_prod_psl_7_psl_19_7_orb3_s1.txt (sha256 b177732333fcc80f0acdded0a1e9dcab1fea64c6e8b6274a3133b41d9d967a02).
  N = 4,021,920 = |PSL(2,7) × PSL(2,19) × Z_7|. ORBIT="3 2 2", μ = 33.2, |Fix(α)| = 26, 790,065 evaluations, 3,823 s.
  Log: research/structured/runs/raise2-d8D10/prod_psl_7_psl_19_7_s1.log (haar_sym: "full diameter check: OK").
- Independent check: research/frontier/build_haar2.py (≤ 20M vertices reference), log build_haar2_p7_19_7.log. PENDING at the time of writing.
