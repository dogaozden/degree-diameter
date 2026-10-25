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
