# Cell (14,10): raise the record (job raise-14-10)

Branch: claude/raise-d14d10-record-2b14g4. Start point: record 1,326,627,120 = 2N, N = |SL(2,139) x Z_247| = 663,313,560
(research/frontier/sols/d14D10_sl_139_247_orb3_FAST1_s1.txt; orbit k=3, m=4, f=2; found at mu = 20.0 in 553 evals).

## Setup and constraints

- Machine: 4 cores, 15 GB RAM. haar_sym FAST=1 uses about 6.3 GB RSS at N ~ 6.6e8 (setup about 30 s), so only one
  or at most two such runs fit at once. Parallelism is therefore THREADS=4 inside one process (candidate evaluations
  are split across threads), not four separate processes.
- Targets: any N > 663,313,560 (vertices > 1,326,627,120). Order of attack: smallest N above the record first, since mu
  grows fast with N (mu = N exp(-W/N), W = 14 * 13^8).
- Wall (STRUCTURE.md, section 3/7): k = 3 orbit search is expected to hit a wall near mu = 45-50 (about N = 6.9e8).

## Candidate queue (orb_screen.py --list, N in [663,313,561, 760,000,000], plain and product groups)

| N | 2N | mu | group |
|---|---|---|---|
| 664,460,400 | 1,328,920,800 | 20.6 | SL(2,151) x Z_193 (first probe) |
| 663,659,724 | 1,327,319,448 | 20.1 | PSL(2,157) x Z_343 |
| 663,978,216 | 1,327,956,432 | 20.3 | PSL(2,263) x Z_73 |
| 665,944,944 | 1,331,889,888 | 21.5 | SL(2,137) x Z_259 |
| 668,104,752 | 1,336,209,504 | 22.8 | SL(2,457) x Z_7 |
| 668,932,320 | 1,337,864,640 | 23.3 | SL(2,239) x Z_49 |
| 668,489,640 | 1,336,979,280 | 23.0 | PSL(2,169) x Z_277 |
| 663,373,728 | 1,326,747,456 | 20.0 | A4 x PSL(2,137) x Z_43 (product, small first factor) |

## Result so far

- **RAISED: (14,10) >= 1,341,781,320** (N = 670,890,660 = |PSL(2,331) x Z_37|, orbit k=3, m=4, f=2, mu = 24.5, 641 evals,
  821 s, fix = 164). Solution research/frontier/sols/d14D10_psl_331_37_orb3_s2_n1341781320.txt; independent check
  research/structured/runs/d14D10_psl_331_37_orb3_s2.lowmem.txt (haarcheck_psl, VALID d=14 D=10, ecc 10 both sides).
  Supersedes 1,333,450,080 (PSL(2,271) x Z_67). Start of session 1,326,627,120, so this session gained +15,154,200 (+1.14 %) in 5 solved steps.

- **RAISED: (14,10) >= 1,333,450,080** (N = 666,725,040 = |PSL(2,271) x Z_67|, orbit k=3, m=4, f=2, mu = 21.9, 169 evals,
  234 s, fix = 134). Solution research/frontier/sols/d14D10_psl_271_67_orb3_s2_n1333450080.txt; independent check
  research/structured/runs/d14D10_psl_271_67_orb3_s2.lowmem.txt (haarcheck_psl, VALID d=14 D=10, ecc 10 both sides).
  Supersedes 1,329,489,288 (PSL(2,163) x Z_307, below).

- **RAISED again: (14,10) >= 1,329,489,288** (N = 664,744,644 = |PSL(2,163) x Z_307|, orbit k=3, m=4, f=2, mu = 20.8,
  1,649 evals, 1,474 s, fix = 80). Solution research/frontier/sols/d14D10_psl_163_307_orb3_s2_n1329489288.txt; independent
  check research/structured/runs/d14D10_psl_163_307_orb3_s2.lowmem.txt (haarcheck_psl, VALID d=14 D=10, ecc 10 from both sides).
  Running record is now 1,329,489,288 (was 1,327,956,432 before this, 1,326,627,120 at the start).

- **RAISED: (14,10) >= 1,327,956,432** (was 1,326,627,120, +1,329,312, +0.10 %). PSL(2,263) x Z_73, N = 663,978,216,
  orbit k=3, m=4, f=2, mu = 20.3, solved in 153 evals (215 s, 4 threads, seed 2). Solution:
  research/frontier/sols/d14D10_psl_263_73_orb3_s2_n1327956432.txt. Checks: research/structured/runs/d14D10_psl_263_73_orb3_s2.lowmem.txt
  (tools/haarcheck_psl, independent low-memory BFS from both sides, VALID d=14 D=10, ecc 10). build_haar2.py not run
  (above its memory limit); the coordinator re-checks.

## Log

- probe 1: SL(2,151) x Z_193 (N = 664,460,400, mu = 20.6), FAST=1, THREADS=4, 600 s: 745 evals (about 0.8 s each,
  so THREADS=4 is about 4-7x faster per evaluation than the single-thread record runs). Best cost 4, not solved.
  RSS 9.4 GB during the search: one run at a time.
- queue 1 (runs/jobs1.txt, orbq.sh, 3000 s per job, seed 2): PSL(2,263) x Z_73, SL(2,151) x Z_193, PSL(2,157) x Z_343,
  SL(2,137) x Z_259. Started 07:29 UTC. Results appear in runs/ (logs) and are copied to research/frontier/sols/ if VALID.
- PSL(2,157) x Z_343 (N = 663,659,724) is below the raised record: skipped (marker log in runs/).
- queue 2 (jobs2.txt, chained after queue 1): PSL(2,199) x Z_169, SL(2,137) x Z_259, PSL(2,271) x Z_67.
  Rule: only N above the current record is worth a run.
- queue 1 results: SL(2,151) x Z_193 (seed 2, 3000 s): best cost 3 after 3209 evals, NOT solved (fix = 149).
  SL(2,137) x Z_259 was stopped after a few minutes (cost not recorded) so the queue could move to PSL candidates.
- Observation: PSL(2,q) has about q/2 fixed points of alpha, SL(2,q) about q. The solved PSL(2,263) x Z73 had fix 131;
  the unsolved SL(2,151) x Z193 had fix 149 and stuck at cost 3. Queue 2 is therefore PSL first:
  PSL(2,163) x Z_307 (N 664,744,644), PSL(2,199) x Z_169, PSL(2,271) x Z_67, PSL(2,169) x Z_277 (all 3000 s, seed 2).
  Started 08:27 UTC.
- PSL(2,163) x Z_307 solved (N 664,744,644), see Result so far. Queue 2 continues: PSL(2,199) x Z_169 started 08:53.
- PSL(2,199) x Z_169 (N 665,893,800): 2,964 s, best cost 3 after 1,401 evals, not solved (fix 98). A retry with ORBW=3 is
  in queue 3.
- PSL(2,271) x Z_67 solved (see Result so far). Queue 2 continues with PSL(2,169) x Z_277; queue 3 chained after it.
- PSL(2,169) x Z_277 (N 668,489,640, mu 23.0): 2,991 s, best cost 3, 3,017 evals, fix 83. Not solved.
- PSL(2,257) x Z_79 (N 670,486,272, mu 24.3): 2,965 s, best cost 3, 2,145 evals, fix 128. Not solved.
  Both stall at cost 3 (one uncovered orbit, or one fixed point at weight 3). Queue 3 continues: PSL(2,173) x Z_259
  (started 11:32), then PSL(2,331) x Z_37.
- Pattern so far: solved PSL cases at mu 20.3-21.9 needed 150-1,650 evals; mu 20.8 solved with fix 80. Each unsolved
  rung ended at cost 3 after about 1,200-3,000 evals.
- PSL(2,173) x Z_259 (N 670,491,948): 2,990 s, best 3, 3,145 evals, fix 86. Not solved.
- PSL(2,331) x Z_37 (N 670,890,660, mu 24.5): SOLVED in 641 evals (821 s), see Result so far. Queue 3 is finished.
- Session stop: about 6 hours of work (06:50 to 12:55 UTC). The queue is empty. Next candidates, all above
  670,890,660 and PSL-first: PSL(2,157) x Z_349 (675.3M, mu 27.6), PSL(2,281) x Z_61 (676.7M, mu 28.7),
  PSL(2,163) x Z_313 (677.7M, mu 29.5). Expect 3,000-7,000 evals at this mu, about 1-2 h each on one run.

## Round 2 (job raise2-14-10, branch claude/raise-d14d10-record-2-3vy08n)

- Start point: the round-1 record 1,341,781,320 (N = 670,890,660, PSL(2,331) x Z_37, fix 164, VALID). The round-2
  brief's 1,326,627,120 is out of date: round 1 had already raised it. Round 1 branch merged into this branch (merge
  commit, no rebase).
- Bar to beat: any N > 670,890,660 (vertices > 1,341,781,320).
- Machine note: two haar_sym runs at N ~ 6.8e8 were OOM-killed during the wide-rows setup (one process reached 9.4 GB
  RSS, the 16 GB box has no room for two). Only one run at a time, THREADS=4.
- Queue (runs/ in r2/): PSL(2,157) x Z_349 (N 675,268,932, mu 27.6, fix 77), then PSL(2,281) x Z_61 (N 676,726,680,
  mu 28.7). Seed 2, 5400 s each. Next on the ladder: PSL(2,163) x Z_313 (677.7M, mu 29.5).
- Not retried: the round-1 cost-3 stalls (PSL 169x277, 257x79, 173x259, 199x169) are all below 670,890,660 and cannot
  improve the record.
- 14:27 PSL(2,157) x Z_349 (seed 2, THREADS=4): OOM-killed (kernel) at 14:29 right after setup, no search lines.
  Single run, 16 GB box: the wide-rows setup plus 4 threads peaks above what fits with other jobs running. Rerun later
  (seed 2, THREADS=2 if memory is tight).
- 14:29 PSL(2,281) x Z_61 (N 676,726,680, mu 28.7, fix 140), seed 2, THREADS=4: RSS 12.5 GB, running. At 1,709 s:
  2,329 evals, best cost 7.
- 16:00 PSL(2,281) x Z_61 (N 676,726,680, mu 28.7, fix 140), seed 2, 5400 s: NOT solved. Final best 6 after 7,305 evals
  (cost 7 from about 1,700 s, 6 from about 5,300 s). A higher fix count than the solved PSL 271 and 331 cases
  (fix 134, 164), so fixed points are not the whole story; mu 28.7 is near the edge of the 5400 s budget.
- 16:00 PSL(2,157) x Z_349 retry, seed 2, THREADS=2 (lower memory), 5400 s.

## Round 2 result

- **RAISED: (14,10) >= 1,350,537,864** (N = 675,268,932 = |PSL(2,157) x Z_349|, orbit k=3, m=4, f=2, mu = 27.6,
  fix = 77). Solved at 2,897 evals (2,114 s, THREADS=2, seed 2). Solution:
  research/frontier/sols/d14D10_psl_157_349_orb3_s2_n1350537864.txt. Checks: haar_sym full diameter OK; independent
  low-memory haarcheck_psl VALID d=14 D=10, 14-regular simple, ecc 10 from both sides (log:
  research/structured/runs/d14D10_psl_157_349_orb3_s2.log). The coordinator re-checks.
  Supersedes 1,341,781,320 (PSL(2,331) x Z_37). Session gain so far: +23,910,544 (+1.8 %) over 1,326,627,120.
- Lesson: fix = 77 (the lowest of the mu 27-29 candidates) solved in 2.9k evals, while PSL(2,281) x Z_61 (fix 140)
  stalled at cost 6 after 7.3k evals. Low |Fix(alpha)| looks like the better predictor than mu alone at this size.
