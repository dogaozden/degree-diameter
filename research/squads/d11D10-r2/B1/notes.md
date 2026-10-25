# Card B1: PREF=1 small-orbit prefilter for RANDORB (round d11D10-r2)

## What changed
Copy: `B1/haar_sym_B1.c` (from `research/structured/haar_sym.c`, unchanged apart from the block below). Build:
`gcc -O3 -march=native -fopenmp -o haar_sym_B1 haar_sym_B1.c -lm`.

- New block before `orbit_main`: `pref_targets` (least element of every alpha-orbit of size < k; only z-classes whose
  z -> AR z orbit is shorter than k are scanned, which is z = 0 for AR = 2, k = 10), `pref_setup`, `pref_eval`, `cov_of`.
- `pref_eval` (meet in the middle, D even): U4 = {s_a s_b^-1 s_c s_d^-1} (d^4 products), X5 = U4 s_e (d^5 products, a bitset
  over G, cleared after each sample). A target t is covered from (e,A) within D-1 iff u t is in X5 for some u in U4
  (U4 is closed under inverses; e in S pads shorter words). Only group products, no tables, no RNG draws.
- RANDORB loop: the orbit is drawn first; with PREF=1 a sample whose prefilter fails is recorded as 1 (RANDB: RANDBV) and
  skips the 10 table builds and the BFS. Samples that pass are evaluated exactly as before (same RNG sequence).
- `PREFCHECK=1` (validation): no early exit, full evaluation of every sample, and each target's MITM coverage is compared
  with the BFS coverage (bit of V[1]); also compared: the pass verdict against "all targets covered in the BFS".
- `RANDLOG=file`: per-sample lines `t cost pass`.
- Env: `PREF=1` (needs D even; D = 10 here). Nothing else changes.

## Targets, psl 243 x Z11, ORBIT="10 1 1" AFROB=1 AFROBH="0 1 2 0" AR=2
55 small-orbit targets: 3 of orbit size 1, 4 of size 2, 48 of size 5 (one representative per alpha-orbit).
Setup: 11.8 s (one scan of the 7.18M elements with z = 0). Expected misses per random sample (Poisson model,
e^(-lambda/|stab|)): 3 x 0.245 + 4 x 0.06 + 48 x 0.0009 = about 1.0, so about 63 % of samples are rejected. Measured: 68 %.

## Validation (same seed 7, RANDORB=100)
- Run `PREF=1 PREFCHECK=1` (`valB.log`, per-sample `valB.txt`): mismatches = 0 (all 55 targets x 100 samples: MITM
  coverage equals BFS coverage), violations = 0 (no rejected sample has cost 0). Rejected 68 of 100; the smallest full
  cost among rejected samples is 24; 32 samples pass.
- Its RANDORB summary (min 24, p1 31, p10 63, median 111, hist, cost0 = 0 of 100) is the full-cost summary of the same 100
  samples; compared with the unmodified stock binary on the same settings: not run (queued, killed at hand-back).
- Among the 32 passing samples, 14 are degenerate (cost >= 10^6, about 70 % of N uncovered). The small-orbit test cannot
  reject them (their small-orbit targets are covered), so they are fully evaluated.

## Timings (RANDB=1 in both, seed 7, RANDORB=200, loop time after setup)
NOT MEASURED. The timing pair (no PREF and PREF, RANDB=1, RANDORB=80) and the stock-binary reference (RANDORB=100) were queued at the gate from 13:05 and never got a slot before the time box ended; they were killed at hand-back, so no seconds-per-sample figure exists.
Known: the PREFCHECK run took 51.0 s for 100 full evaluations (about 0.5 s each: 10 table builds plus BFS); pref_setup takes 11.8 s once; the per-sample prefilter cost (d^5 = 161,051 products) is not measured.

## Next (not done, card scope)
A cheap second probe would also reject the degenerate samples: test a few random generic elements with the same MITM
(each covered probe costs about 500 products, a degenerate sample fails a probe with probability about 0.7). Probes never
reject a sample of cost 0. Untested.
