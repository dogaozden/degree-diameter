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
