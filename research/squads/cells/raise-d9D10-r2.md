# Cell (Δ, D) = (9, 10): job raise2-9-10 (round 2, Haar worker, Haiku 5.5)

Branch `claude/raise-d9d10-r2-...` (round-2 branch). Round 1 is on `claude/raise-d9d10-record-7f9el2`; its notes are
research/squads/cells/raise-d9D10.md there.

## Record bar (discrepancy)

The brief says our record is 23,975,280. Round 1's branch holds a VALID record of **24,099,600 vertices**
(psl 151 × Z7, N = 12,049,800, file research/frontier/sols/d9D10_psl_151_7_orb3f0_s1.txt, sha256 d78ef086…c654),
checked by haar_sym's full check and by haarcheck_psl. The coordinator's check was pending. This round aims to beat
**24,099,600** (N > 12,049,800). Beating 23,975,280 is already done by that file.

## What round 1 tried (do not repeat)

- orbit k = 3, m = 3, f = 0 (haar_sym ORBIT="3 3 0") on PSL/SL/PGL-type groups with N in (11.99M, 12.08M]:
  psl 151×Z7 (SOLVED, 4.3e5 evals), psl 41×Z349 (dropped early), sl 43×Z151 (below N; cost 3 after 3.2e5),
  psl 79×Z49 (cost 3–4 in 4 seeds, ORBW=3 too), prod sl 8×psl 19×Z7 (cost 3–4), sl 73×Z31 ORBW=3 (cost 1 after 3.5e5, one fixed element).
- Screen (300 samples per group) of N > 11,987,640 (orb_screen.py).

## Not tried in round 1 and chosen for round 2

- sl 73 × Z31 again, new seed, with ORBW=3 (round 1's closest miss, N 12,057,264, μ 36.0).
- psl 289 × Z1 (PSL(2,17²), N 12,068,640, μ 36.5): PSL is fine at even D; no Z-part, so no z-collision issue.
- pgl 73 × Z31 (N 12,057,264, μ 36.0): PGL(2,73), same order as sl 73 but a different group.
- Screen of all groups with N in (12,049,801, 12,200,000], 500 random symmetric S each (screen log: runs/raise9-10-r2/screen/).

## Log

- (start) 15:1x UTC: haar_sym, hc2, hcsl and tools/haarcheck_psl built here. Runs a (sl 73×Z31, ORBW=3, seed 21),
  b (psl 289×Z1, seed 1), c (pgl 73×Z31, seed 1) started, 4.4 h each, 1 thread each. Screen running in background.
- Screen (500 random symmetric S per group, N in (12,049,801, 12,200,000], μ 36.0–42.2): ranking by (p1+p10)/2:
  psl 79×Z49 (μ 36.8, min 16, p1 21, p10 36, fix 38) > prod sl 8×psl 19×Z7 (μ 36.3, min 17, p1 24, p10 34) >
  sl 73×Z31 (μ 36.0, min 18, p1 24, p10 37) > pgl 73×Z31 (μ 36.0, min 19, p1 25, p10 38) > psl 53×Z163 (μ 39.0, min 18, p1 27, p10 44).
  psl 289×Z1 (μ 36.5, min 21, p1 31, fix 143) is weak. Calibration (round 1, psl 151×Z7, the record): min 13, p1 19, p10 33.
  No new candidate beats the calibration on the screen; the screen does not rule out a solve in them.
- 15:10 UTC: psl 289 run stopped after 120 s (screen weak).
- 15:12 UTC: started d = psl 79×Z49 seed 5 (plain). Screen done.
- 15:19 UTC: started e = prod sl 8×psl 19×Z7 seed 31, ORBW=3.
- 15:2x UTC status (wall-clock, 80–85 evals/s per run): a sl 73×Z31 ORBW=3 seed 21: best 3 at 5.2e4 evals;
  c pgl 73×Z31 seed 1: best 7 at 5.1e4; d psl 79×Z49 seed 5: best 4 at 4.0e4; e prod sl 8×psl 19×Z7 ORBW=3 seed 31: best 16 at 1.4e3 (just started).
  Each run has a 15,840 s budget (about 4.4 h), so about 1.2–1.3 million evaluations.
- 18:50 UTC status: no solve. a sl 73×Z31 ORBW=3 (seed 21): best 3 at 1.1e6 evals; c pgl 73×Z31 (seed 1): best 3 at 1.1e6;
  d psl 79×Z49 (seed 5): best 3 at 1.1e6; e prod sl 8×psl 19×Z7 (ORBW=3, seed 31): best 3 at 5.7e5.
  All four have sat at cost 3 for more than an hour (since about 17:20 UTC): the cost-3 floor is the same as round 1's
  sl 73×Z31 and psl 79×Z49 runs (round 1: cost 1 and 3). Each run ends at its 15,840 s budget, about 19:35 UTC.

## Final status (19:44 UTC): no new record

All four 15,840 s runs finished with no solution (every run is still at cost 3 at the end):

| run | group | N | seed / flags | best cost | evals |
|---|---|---|---|---|---|
| a | sl 73 × Z31 | 12,057,264 | 21, ORBW=3 | 3 | 1.33e6 |
| c | pgl 73 × Z31 | 12,057,264 | 1 | 3 | 1.30e6 |
| d | psl 79 × Z49 | 12,077,520 | 5 | 3 | 1.32e6 |
| e | prod sl 8 × psl 19 × Z7 | 12,065,760 | 31, ORBW=3 | 3 | 0.72e6 |
| b | psl 289 × Z1 | 12,068,640 | 1 (killed at 120 s) | 17 | 5e3 |

Record stands at 24,099,600 (round 1, psl 151 × Z7). No new record in this round.

What this round shows:
- Four different groups with N in (12.05M, 12.08M] all stall at cost 3 (one orbit uncovered, or one fixed element) after
  0.7–1.3 million evaluations, with the plateau reached by about 17:20 UTC. Round 1's psl 151×Z7 solved at 4.3e5 evals,
  so the N = 12.05M band is not uniformly hard; the solve is a lucky draw.
- The screen does not separate these groups from round 1's calibration group by much (min 16–19 vs 13).
- psl 289 × Z1 (PSL over GF(17²)) screened badly (fixed set 143, p1 31) and was stopped.

Suggested next steps (for the coordinator):
- The round-1 psl 151 × Z7 record is still the bar. A new record needs N > 12,049,800 with cost 0; the band above it is
  already screened (research/structured/runs/raise9-10-r2/screen/).
- More seeds on psl 151×Z7-like groups at N just above 12,049,800 would be the next-best use of compute; each 4.4 h run here
  gives about 1.3e6 evals, and round 1 needed 4.3e5 for its solve.
- The orbit method's plateau at cost 3 from 17:20 UTC onward suggests that a different annealing move (targeted moves on
  uncovered elements) or a different α is needed for the next rung. Not tried in this round.
