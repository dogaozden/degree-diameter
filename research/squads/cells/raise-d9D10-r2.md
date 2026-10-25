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
