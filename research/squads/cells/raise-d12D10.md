# Cell (Δ, D) = (12, 10): raise our record (job raise-12-10)

Record to beat: **325,832,976** vertices = 2·|SL(2,107) × Z_133|, Haar graph, orbit search k = 3, m = 4, f = 0
(`../../frontier/sols/d12D10_sl_107_133_orb3f0_s1.txt`; rebuilt by tools/harvest.py, see
`../../frontier/runs/harvest_check_2026-10-23.txt`). Table value 300,383,050; Moore bound 5,187,484,920.

## Method

- Search: `research/structured/haar_sym` with `ORBIT="3 4 0"` (S = 4 free orbits of an order-3 automorphism α =
  conjugation by an order-3 element × z ↦ r·z on Z_n; no identity, the solution is normalised so s₀ = e).
  Command: `ORBIT="3 4 0" THREADS=1 ./haar_sym 12 10 <secs> <seed> 8 <out> psl|sl <q> <n>`.
- Queue: `research/structured/tools/orbq.sh JOBFILE OUTDIR` (one job per line; each solution is re-checked and the verdict
  appended to its log). Checkers above 20M vertices: `tools/hcsl` + `tools/hc2` (SL), `tools/haarcheck_psl` (PSL).
- Target order from `research/structured/tools/mu_plan.py` / `orb_screen.py --list` (μ = N e^(−W/N); W fixed for (12,10)).
  Reference points: μ 20 ↔ 2N = 325.98 M, μ 30 ↔ 333.98 M, μ 40 ↔ 339.9 M (the record sits at μ = 19.8).
- Memory: haar_sym wide rows are about 1.0–1.3 GB per process at N ≈ 163 M for prime q ≤ 300. Prefer smaller q and
  larger n (SL(2,q) tables cost ~12 q³ bytes; SL(2,691) would be ~4 GB).

## Rungs

Rung 1 (μ ≈ 20–24, 900 s per job, seed 1, groups above the record order, prime q ≤ 300):
psl 137×127, sl 79×331, psl 293×13, sl 139×61 (first four, running 07:21 UTC), then sl 131×73, sl 103×151, psl 197×43,
sl 109×127, sl 233×13, psl 103×301.

(Log entries below are added as runs finish.)

## Results (rung 1, seed 1, 900 s per job, k = 3, m = 4, f = 0)

| group | N | 2N | μ | best cost | evals | result |
|---|---|---|---|---|---|---|
| sl 79 × Z331 | 163,169,760 | 326,339,520 | 20.4 | 3 | 2,913 | not solved |
| psl 137 × Z127 | 163,272,216 | 326,544,432 | 20.6 | 3 | 1,305 | not solved |
| sl 139 × Z61 | 163,814,280 | 327,628,560 | 21.8 | 2 | 1,233 | not solved |
| psl 293 × Z13 | 163,497,516 | 326,995,032 | 21.1 | 2 | 1,273 | not solved |
| **psl 197 × Z43** | **164,371,284** | **328,742,568** | 22.4 | **0** | **305** | **solved** |

**New record: 328,742,568 vertices** (+0.95 % over 325,832,976).
- File: `../../frontier/sols/d12D10_psl_197_43_orb3f0_s1.txt`; log: `../../structured/runs/d12D10_psl_197_43_orb3f0_s1.log`.
- Checks: haar_sym's own full diameter check (both (e,A) and (e,B) reach all 164,371,284 elements within 10, normalised
  s₀ = e); independent `tools/haarcheck_psl` (2m56s): VALID.
- Not checked: build_haar2.py (above 20M vertices it is too slow for this box); the coordinator re-checks.

Remaining rung-1 jobs (sl 131×73, sl 103×151, sl 109×127, sl 233×13, psl 103×301) are still queued or running.
Observation: the first three unsolved groups plateaued at best cost 2–3 after ~1,300 evals. Solved and unsolved runs
at nearly the same μ look like a group effect, so the next rungs should screen groups before raising μ.

Rung 1 finished (08:08 UTC): 1 solved, 9 unsolved (best costs 2–5 at μ ≈ 20–22, 900 s, 1–3k evals each):
sl 79×331 (3), psl 137×127 (3), sl 139×61 (2), psl 293×13 (2), sl 131×73 (3), sl 233×13 (5), sl 109×127 (5),
sl 103×151 (3), psl 103×301 (3). The one solve, psl 197×43, took 305 evals.

Rung 2 (μ ≈ 25–32, 1500 s, seed 1) running: psl 127×163 (μ 29.8), psl 103×307 (μ 32.2), psl 113×229 (μ 25.1),
sl 97×181 (μ 25.0). Then queued: psl 151×97 (μ 30.0), sl 101×163 (μ 32.9).

Rung 2 finished (10:22 UTC): 0 solved, best costs 4–9 at μ 25–33 with 1,500 s per job (1–5k evals):
psl 127×163 (6), psl 103×307 (6), psl 113×229 (4), sl 97×181 (9), psl 151×97 (6), sl 101×163 (6).
Reading: at μ ≥ 25 a 1,500 s single-seed run does not reach cost 0 on these groups; the rung-1 solve was a lucky draw.

Next round: only groups with N > 164,371,284 can beat the record. Seed 2–3 runs of 3,600 s on
psl 103×301 (164.44 M), sl 109×127 (164.45 M), sl 103×151 (164.99 M) and psl 97×361 (164.72 M).

**New record: 329,972,448 vertices** (sl 103 × Z_151, N = 164,986,224, seed 2, 897 evals, 244 s; +1.26 % over the previous
328,742,568 and +1.28 % over the original 325,832,976).
- File: `../../frontier/sols/d12D10_sl_103_151_orb3f0_s2.txt`; log: `../../structured/runs/d12D10_sl_103_151_orb3f0_s2.log`.
- Checks: haar_sym's own full check (both generators reach all N within 10); independent `tools/hcsl` and `tools/hc2`:
  both VALID (eccA = eccB = 10).

Also solved (below the record, kept as a valid cell solution): **psl 97 × Z_361**, N = 164,719,968, 329,439,936 vertices,
seed 1, 5,121 evals, 2,109 s. File `../../frontier/sols/d12D10_psl_97_361_orb3f0_s1.txt`, log in `../../structured/runs/`.

Seed-2 round (3,600 s each, unless noted): psl 103×301 (164.44 M): not solved, best 3, 9,193 evals. sl 109×127
(164.45 M): not solved, best 3, 5,001 evals. psl 113×229 (165.20 M, seed 2): see the end of this file.
psl 97×361 (164.72 M, seed 1) solved above; its independent PSL check: VALID.

## Final round and where it stopped (13:03 UTC, six-hour window)

Seed-2 psl 113×229 (165.20 M, 3,600 s): not solved, best 3, 4,553 evals.
Final round (2,700 s each): psl 107×271 (165.98 M): best 6, 5,281 evals; sl 79×337 (166.13 M): best 3, 8,001 evals;
sl 157×43 (166.40 M): best 6, 2,289 evals; sl 97×181 seed 2 (165.18 M): best 3, 2,593 evals. None solved.

**Stopped.** Current record: **329,972,448 vertices** (sl 103 × Z_151, N = 164,986,224, seed 2, checked by haar_sym,
`tools/hcsl` and `tools/hc2`). Other verified finds: psl 197 × Z_43 (328,742,568) and psl 97 × Z_361 (329,439,936,
PSL checker VALID), both in `../../frontier/sols/`.

Why: this cell, with the orbit method at k = 3, m = 4, f = 0, now needs solves in a narrow band (N just above 164.99 M,
μ ≈ 22–28). Across 25 jobs at μ ≈ 20–33 (900–3,600 s), 3 solved: psl 197×43 (μ 22.4, 305 evals), sl 103×151 seed 2 (μ 24.5,
897 evals) and psl 97×361 (μ 23.9, 5,121 evals). The unsolved jobs at μ ≥ 25 ended with best cost 3–9 after 1–9k evals. Going further needs many more seeds per
group (roughly 10–20 hours of single-core time for a few more percent), or a new idea: a different automorphism, or ORBW /
RESTART variants on the same groups. The coordinator decides whether a bigger model is worth it.

## Round 2 (job raise2-12-10, branch claude/raise-d12d10-record-r2-gkgabg)

Starting record (as given in the round-2 brief): 325,832,976. Round 1's branch reports 329,972,448 (sl 103 × Z_151),
so that is the bar this round started from; the coordinator should reconcile the two numbers.

Queue: `research/structured/spool_r3/` (pool.sh, 4 slots, 2400 s per job, seed 3, k = 3, m = 4, f = 0). Two variants per
group: ORBW=3 (uncovered fixed element weighs 3) and the default. Groups: N in (164,986,224, 166,100,000], prime q, n with all
prime factors ≡ 1 mod 3, n ≤ 500 (round 1's untried sl/psl groups; prod and pgl groups are not run, no checker for them).

**New record: 330,588,720 vertices** = 2 · |PSL(2,89) × Z_469|, N = 165,294,360, seed 3, ORBW=3, 2,521 evals, 839 s,
μ = 25.3, |Fix| = 44.
- File: `../../frontier/sols/d12D10_psl_89_469_orb3f0_ORBW3_s3.txt`; log: `../../structured/runs/d12D10_psl_89_469_orb3f0_ORBW3_s3.log`.
- Checks: haar_sym's own full diameter check (both generators reach all N within 10; normalised s₀ = e); independent
  `tools/haarcheck_psl` (the queue's checker, ~4 min): VALID, 330,588,720 vertices.
- Not checked: build_haar2.py (above 20M vertices); the coordinator re-checks.

Note on ORBW=3: this solve used ORBW=3. The same group with the default weight (job 11-psl_89_469_def, seed 3) was at cost 6
at ~3,000 evals when it was last seen; one solve is not a measured advantage for ORBW=3.

**New record: 332,158,176 vertices** = 2 · |SL(2,73) × Z_427|, N = 166,079,088, seed 3, default weight (no ORBW), 5,153 evals,
960 s, μ = 25.3, |Fix| = 71. This beats 330,588,720 (psl 89 × Z_469, above).
- File: `../../frontier/sols/d12D10_sl_73_427_orb3f0_s3.txt`; log: `../../structured/runs/d12D10_sl_73_427_orb3f0_s3.log`.
- Checks: haar_sym full diameter check (both generators reach all N within 10; normalised s₀ = e); independent
  `tools/hcsl` and `tools/hc2`: both VALID (eccA = eccB = 10).
- Not checked: build_haar2.py (above 20M vertices); the coordinator re-checks.
- The same group with ORBW=3 (seed 3) was still running at cost 3 when this solve landed. Solves so far: 2 of the first 12 jobs.

## Round 2: all jobs and where it stopped

Record at the end of round 2: **332,158,176** = 2 · |SL(2,73) × Z_427| (see above). Three verified records this round:
330,588,720 (psl 89 × Z_469, ORBW=3), 332,158,176 (sl 73 × Z_427, default weight). The 329,972,448 of round 1 is superseded.

All orbit jobs (k = 3, m = 4, f = 0, seed 3, 2400 s, K = 8, THREADS = 1; `spool_r3/`; logs and per-job queue logs there):

| N | group | μ | best cost (ORBW=3 / default) | evals | result |
|---|---|---|---|---|---|
| 165,294,360 | psl 89 × Z_469 | 25.3 | 0 (2,521) / 3 (7,033) | | **solved (ORBW=3)** |
| 165,679,920 | sl 71 × Z_463 | 25.3 | 6 / 3 | 8,000 | not solved |
| 166,079,088 | sl 73 × Z_427 | 25.3 | 3 / **0** (5,153) | | **solved (default)** |
| 166,284,888 | sl 67 × Z_553 | | 3 / 3 | 12,000 | not solved |
| 167,457,696 | psl 97 × Z_367 | | 6 / 3 | 5,300 | not solved |
| 167,692,140 | psl 109 × Z_259 | | 6 / 6 | 8,000 | not solved |
| 167,826,960 | sl 71 × Z_469 | | 6 / 9 | 13,300 | not solved |
| 168,089,064 | sl 67 × Z_559 | | 9 / 9 | 10,700 | not solved |
| 168,366,828 | psl 83 × Z_589 | | 6 (default) | 8,900 | not solved |
| 168,412,752 | sl 73 × Z_433 | | 12 (default) | 8,800 | not solved |
| 168,697,200 | sl 151 × Z_49 | | 4 (default) | 6,400 | not solved |
| 169,085,280 | sl 79 × Z_343 | | 3 (default) | 9,300 | not solved |
| 169,428,600 | psl 199 × Z_43 | | 4 (default) | 5,600 | not solved |
| 169,523,640 | psl 89 × Z_481 | | 9 (default) | 9,000 | not solved |
| 169,653,636 | psl 107 × Z_277 | | 12 (default) | 6,200 | not solved |
| 169,720,980 | psl 131 × Z_151 | | 9 (default) | 3,900 | not solved |
| 169,876,080 | sl 89 × Z_241 | | 12 (default) | 6,500 | not solved |
| 169,991,304 | psl 167 × Z_73 | | 3 (default) | 5,700 | not solved |
| 166,332,360 | sl 61 × Z_733 | | 9 (default) | 7,300 | not solved |
| 166,574,520 | psl 71 × Z_931 | | 3 (default) | 13,400 | not solved |
| 166,514,520 | sl 59 × Z_811 | | 6 (default) | 7,100 | not solved |
| 167,051,448 | psl 73 × Z_859 | | 9 (default) | 4,200 | not solved |

The μ column is the same for every group at about 25; it is N e^{−W/N} with W fixed for (12,10), so it moves only slowly.

**Read-out.** Two solves in 23 groups (about 40 jobs at 2,400 s each plus one shorter run). Both solves came at the bottom of the window
(N = 165.3 M and 166.1 M). At N ≥ 166.3 M no run got below cost 3, and most stalled at 6–12: the free-orbit misses
(μ/3 ≈ 8) dominate, as STRUCTURE.md predicts. ORBW=3 did not clearly help: one solve each way, and in pairs the weighted
run was not systematically better. Round-1's open leads were: many more seeds per group, and ORBW/RESTART variants. This
round tried ORBW=3 (one run per group), new groups and one seed; RESTART=1 was not run.

**Why I stopped.** About six hours of wall time were used (14:23–19:27 UTC). The untried groups above the record are now the
ones with n > 500 (for example psl 79 × Z_679, sl 61 × Z_739), and a final batch on four of them (n = 733, 811, 859, 931) gave best
costs 3–9 with no solve. The next step with a real chance is more seeds on the two bottom-of-window groups above the record
(sl 73 × Z_427 seed 4, psl 89 × Z_481 seed 4, sl 67 × Z_553 seed 4), and RESTART=1 on the cost-3 groups (sl 67 × Z_553, sl 79 × Z_343,
psl 167 × Z_73, psl 71 × Z_931). Those would need roughly another 3–4 core-hours. Non-Haar (prod) groups were not run: there is no
independent checker for them yet.

**Checks.** Every record above passed haar_sym's own full diameter check and an independent checker: `tools/haarcheck_psl`
(psl 89 × Z_469) and `tools/hcsl` + `tools/hc2` (sl 73 × Z_427, both eccentricities 10). The coordinator should re-check both.

---

## Round 3 (job raise3-12-10, branch claude/raise-d12d10-record-r3-82qxos)

**Bar at the start of round 3.** The brief said 325,832,976 (the original record). Round 2's branch holds
**332,158,176** = 2·|SL(2,73) × Z_427| (`../../frontier/sols/d12D10_sl_73_427_orb3f0_s3.txt`, checked by haar_sym, `tools/hcsl`,
`tools/hc2`). This round starts from 332,158,176 and every step must exceed it. The coordinator should reconcile the number.

**Where round 2 left off (its own open leads).** Seeds 4 on the bottom-of-window groups (sl 73×427, psl 89×481, sl 67×553),
RESTART=1 on the cost-3 groups (sl 67×553, sl 79×343, psl 167×73, psl 71×931), and groups above the record. Round 2 did not run
prime-power q (`orb_screen.py` enumerates them; `haar_sym` supports GF(p^e) through `make_field`).

**μ.** `orb_screen.py 12 10 166079089 168400000 "3 4 0" --list --nmax 2000 --fams sl,psl` puts the current record at μ ≈ 27.5
and the window above it at μ 27.5–33 (N = |G| between 166.1 M and 168 M). The round 2 table quoted μ ≈ 25 for the same
groups; the two μ conventions differ, and this round uses `orb_screen`. A μ step of ~1 costs roughly a factor 2 in evaluations
(round 2's solves came at μ 22–25).

**Queue.** `research/structured/spool_r4/` (`tools/pool.sh`, 4 slots, one job per file, 2400 s, seed 4, K = 8, THREADS = 1,
k = 3, m = 4, f = 0). Job list is the file names there. Groups are the 38 SL/PSL candidates in the window with n ≤ 2000; 18 are
queued first (cost-3 groups with RESTART=1 or ORBW=3; new groups; prime-power q).

Checkers: prime-q SL uses `tools/hcsl` and `tools/hc2`, prime-q PSL uses `tools/haarcheck_psl`. Prime-power q (sl 81, sl 64,
sl 49) has no independent checker yet; a solve there needs one before it can be recorded.

*Status:* (see the entries below, appended as runs finish.)

*Checker for prime powers:* `tools/haarcheck_pp.c` (generic GF(q), same definitions and BFS as `frontier/haarcheck_sl.c`,
field built as in haar_sym.c, header polynomial checked against it). Verified: VALID on the prime record sl 73 × Z_427
(ecc 10 from both sides), and VALID on a GF(8) test cell sl 8 × Z_19 (d7 D8, build_haar2.py also VALID). `orbq.sh` still
sends prime-power headers to hcsl/hc2 (prime-only); a prime-power solve must be checked with `haarcheck_pp` by hand.
