# Cell (Δ, D) = (9, 10): job raise-9-10 (Haar worker, Haiku 5.5)

Branch `claude/raise-d9d10-record-7f9el2`. Goal: beat our record **23,975,280 vertices** (|G| = 11,987,640,
PSL(2,71) × Z67, orbit k=3, m=3, f=0; file research/frontier/sols/d9D10_psl_71_67_orb3f0_s1.txt).
Table 20,017,260. Bipartite Moore bound 306,783,378. W(9,10) = 153,391,689 binding words, so μ = N e^(−W/N).

## Method

Orbit search (research/structured/haar_sym, ORBIT="3 3 0"), built with
`gcc -O3 -march=native -fopenmp -o haar_sym haar_sym.c -lm` (in research/structured/, untracked binary).
Queue: research/structured/tools/orbq.sh, run as `bash orbq.sh JOBS OUTDIR` (the checkout has no +x bit).
Job line: `3 3 0 | 9 10 <secs> <seed> 8 <group> <n>`. One thread per run. Above 10M vertices the queue runs
the low-memory checkers (tools/haarcheck_psl, tools/hcsl, tools/hc2; compiled from frontier/haarcheck_sl.c and haarcheck2.c).
Screen: tools/orb_screen.py 9 10 11987641 12190000 "3 3 0" --samples 300 (log runs/raise_d9D10_screen/).

## Candidate orders (N > 11,987,640, μ ≤ 41; from orb_screen --list)

μ = N e^(−W/N). The record has μ = 33.2 (solved after 1.0·10⁵ evals, 2,445 s, 0.024 s/eval at this N).

| group | N | μ | status |
|---|---|---|---|
| psl 41 × Z349 | 12,019,560 | 34.5 | run A (4 h) |
| sl 43 × Z151 | 11,999,064 | 33.7 | run B (4 h) |
| prod psl 5 × sl 16 × Z49 | 11,995,200 | 33.5 | screened |
| psl 151 × Z7 | 12,049,800 | 35.7 | screened |
| psl 79 × Z49 | 12,077,520 | 36.8 | screened |

## Screen (tools/orb_screen.py, 300 random symmetric S per group, μ ≤ 41; log research/structured/runs/raise_d9D10_screen/)

Calibration: the record group psl 71 × Z67 gives min 15, p1 19, p10 32, median 56 (fix 35).
Top of the ranking by (p1+p10)/2 among N > 11,987,640: psl 151×Z7 (μ 35.7; min 13, p1 19, p10 33, fix 74);
psl 79×Z49 (μ 36.8; min 16, p1 21, p10 36, fix 38); prod sl 8×psl 19×Z7 (μ 36.3; min 19, p1 24, p10 34, fix 80);
sl 229 (μ 34.1; fix 227, bad); prod psl 5×sl 16×Z49 (μ 33.5). Last place: psl 41×Z349 (p1 33, p10 55).

## Log

- 2026-10-25 07:24 UTC: baseline confirmed. haar_sym built. Screen started (RANDORB 300 per group, μ ≤ 41).
  Runs A and B started at 07:25 UTC, 4 h each.
- 07:35 UTC: run A (psl 41×Z349, best 15 after 2.2e4 evals) stopped: weakest on the screen.
  Started C psl 151×Z7, D psl 79×Z49, E prod sl 8×psl 19×Z7 (4 h each, seed 1, K 8).
  Run B (sl 43×Z151) still going, best 6 after 2.6e4 evals.
- 09:25 UTC: no solution yet. Best costs (evals): C psl 151×Z7 cost 1 (2.9e5), B sl 43×Z151 cost 3 (3.2e5),
  E prod sl 8×psl 19×Z7 cost 3 (2.7e5), D psl 79×Z49 cost 6 (4.4e5). About 0.02–0.03 s per eval.
  The runs end at about 11:35–11:45 UTC (4 h each); the first-moment wall for this method is μ ≈ 40–45 (SIZE_LAW §2.3),
  so these μ values (35–37) are within reach but need more evals than we have.
- **10:16 UTC: NEW RECORD (9,10): psl 151 × Z7, 24,099,600 vertices** (N = 12,049,800, orbit k=3 m=3 f=0, fix 74, μ 35.7,
  seed 1, 425,161 evals, 9,648 s). Previous record 23,975,280 (psl 71 × Z67). File: research/frontier/sols/d9D10_psl_151_7_orb3f0_s1.txt
  (sha256 d78ef086c9c0f2ed5a26dc8fb9193208c94557b535ef669eb349d4c50ccac654). Checks: haar_sym full check OK (both
  normalisations), orbq's haarcheck_psl VALID, and an independent re-run of tools/haarcheck_psl: ecc 10 from (e,A) and (e,B),
  all 12,049,800 per side reached. Log: research/structured/runs/d9D10_psl_151_7_orb3f0_s1.log.
  Not yet re-checked by build_haar2.py (too heavy above 10M; the coordinator's check is pending).
- 10:17: stopped run F (psl 151×Z7 ORBW=3, same group, no longer useful) and run B (sl 43×Z151, N below the new record).
- 10:17 UTC: draft PR #350 opened for the branch.
- 10:58 UTC: running E prod sl 8×psl 19×Z7 (N 12,065,760; cost 3, 4.97e5 evals), G psl 79×Z49 ORBW=3 seed 2 (N 12,077,520;
  best 3, 1.65e5), H psl 79×Z49 seed 3 (best 4, 1.66e5). All above the new record's order, so any solve is a new record.
- 12:18–13:13 UTC (final rung): G psl 79×Z49 ORBW=3 seed 2, 2 h: best 3 (4.9e5 evals); H psl 79×Z49 seed 3, 2 h: best 4;
  I sl 73×Z31 ORBW=3 seed 1, 1.5 h: best 1 (3.5e5 evals, one fixed element uncovered); J psl 79×Z49 ORBW=3 seed 4, 55 min:
  best 3 (1.9e5); K prod sl 8×psl 19×Z7 ORBW=3 seed 2, 55 min: best 4 (1.1e5); E prod sl 8×psl 19×Z7 seed 1, 4 h: best 3 (6.0e5).

## Status at 13:13 UTC

**Record: 24,099,600 vertices (psl 151 × Z7), up from 23,975,280. No further solve.** All runs stopped; no process left running.
Draft PR #350 is open for the branch. The coordinator's independent check of the record is pending.

What we know about the next rung (N > 12,049,800, μ > 35.7):
- Every run above that order stalled at best cost 1–4 after 1–5·10⁵ evals (μ ≈ 36–37), in the same way as the wall SIZE_LAW §2.3 and STRUCTURE §5 describe.
  ORBW=3 did not clearly help here (sl 73×Z31 reached cost 1 with a fixed element uncovered, but no more).
- At N ≈ 12M one eval is ~0.024 s, so one 4-hour single-thread run is about 6·10⁵ evals. The record needed 4.3·10⁵.
  Going higher needs several times more evals per run, which is a few more core-days than this session's 6 hours allowed.
- Not tried: RESTART=1 reheats from random orbits on psl 151 × Z7 at higher μ, the k=5 orbit ladder, longer seeds on
  psl 79 × Z49 (cost 3 in several seeds), and the Haar-lift routes in research/theorems/BEAT_16_5_SQUAD.md.
  A bigger model would be the next step if this route is still wanted (per the brief, the coordinator decides).

## Files

- research/frontier/sols/d9D10_psl_151_7_orb3f0_s1.txt (record, sha256 d78ef086…c654)
- research/structured/runs/d9D10_psl_151_7_orb3f0_s1.log (its run log)
- research/structured/runs/raise9-10/ (all queue files and run logs of this session)
- research/structured/runs/raise_d9D10_screen/ (screen output)
