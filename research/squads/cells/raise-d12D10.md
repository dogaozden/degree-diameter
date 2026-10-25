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
