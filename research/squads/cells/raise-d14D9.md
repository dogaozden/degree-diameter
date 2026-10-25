# Cell (Δ, D) = (14, 9): raise job "raise-14-9"

Session: `claude/raise-d14d9-haar-jq8m8d` (Haiku worker, 2026-10-25). Table value 95,087,738 (DS14v2, Table 4).
Bipartite Moore bound 1,767,416,562.

**Record to beat: 116,068,656 vertices** = 2N, N = 58,034,328 = |SL(2,67) × Z193|, orbit search k=3, m=4, f=2
(`research/frontier/sols/d14D9_sl_67_193_orb3_s1.txt`, μ = 14.14, 3,409 evaluations, 1,155 s).

## Method

Orbit-symmetric Haar search (`research/structured/`, `haar_sym.c`): S = {e} ∪ (2 torus generators fixed by α) ∪ (4 free
α-orbits of size 3), α = conjugation by an order-3 element of Q times z ↦ rz on Z_n. Ladder over group orders
N = |Q| · n just above the record, screened with `tools/orb_screen.py 14 9 LO HI "3 4 2" --list`.

Model (`tools/mu_plan.py`, W(14,9) = 883,708,281): μ = N e^(−W/N). Around N = 58M, d ln μ / d ln N ≈ 1 + W/N ≈ 16, so
each +1 % in N multiplies μ by about 1.17:

| μ | N (= |G|) | 2N |
|---|---|---|
| 14.1 | 58.03 M | 116.07 M (record) |
| 16 | 58.4 M | 116.9 M |
| 20 | 59.3 M | 118.6 M |
| 25 | 60.1 M | 120.3 M |
| 30 | 60.8 M | 121.7 M |

Cost model from the record: about 170 · e^(μ/4.7) evaluations at ~0.35 s each (scaled from one solve, very rough).
Four cores, 6 h budget → about 250k evaluations in total, so μ ≈ 25–30 is the practical ceiling for this cell.

Checks: N > 10M (all cells here) use the low-memory checkers `tools/hcsl` + `tools/hc2` (SL) or `tools/haarcheck_psl`
(PSL), built from `research/frontier/haarcheck_sl.c`, `haarcheck2.c` and `research/structured/tools/haarcheck_psl.c`.
`orbq.sh` runs them automatically on any solution above 10M.

Note: `tools/orbq.sh` and `pool.sh` are not executable in this checkout; run them with `bash tools/orbq.sh JOB OUT`.

## Runs

(Log of every run; the coordinator re-checks anything listed as VALID.)

### Wave 1 (μ ≈ 14.2–14.4, seed 1, 1800 s each, 2026-10-25 07:39 UTC)

| group | N | 2N | μ | \|Fix\| | wide rows | result |
|---|---|---|---|---|---|---|
| sl 37 × Z1147 | 58,056,552 | 116,113,104 | 14.23 | 35 | yes (HW 222) | pending |
| sl 31 × Z1951 | 58,061,760 | 116,123,520 | 14.25 | 29 | **no** (fallback, slower) | pending |
| sl 59 × Z283 | 58,105,560 | 116,211,120 | 14.43 | 59 | yes (HW 118) | pending |
| psl 41 × Z1687 | 58,100,280 | 116,200,560 | 14.41 | 20 | yes (HW 241) | pending |
