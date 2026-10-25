# Cell (Δ, D) = (10, 10): raise the record above 60,141,120

Job "raise-10-10" (Haiku worker, cloud session, branch `claude/raise-d10-d10-record-pyapvk`, 2026-10-25).

Table value 50,331,156. Our record 60,141,120 = 2N with N = |SL(2,79) × Z_61| = 30,070,560, k = 3, m = 3, f = 1
(`../../frontier/sols/d10D10_sl_79_61_orb3_s1.txt`, found by the structured search, μ = 15.3, 833 evaluations).
Moore bound 871,696,100. W(10,10) = 435,848,050, so λ = W/N ≈ 14.5 at N ≈ 30M.

## Plan

- μ = N·exp(−W/N) is the planning variable (`../../structured/tools/mu_plan.py`). Reference points for the 2N target:
  μ = 20 ↔ 2N ≈ 61.2M, μ = 25 ↔ 62.1M, μ = 30 ↔ 62.9M, μ = 35 ↔ 63.5M, μ = 40 ↔ 64.1M.
- k = 3 (m = 3, f = 1): the record recipe. Fitted cost grows like e^(μ/4.5) evaluations (STRUCTURE.md §3).
- k = 5 (m = 2, f = 0; 10 = 5·2, so no identity letter): μ_eff = μ/5 + |Fix|·e^(−λ/5). With |Fix| ≈ q ≈ 60–80 this
  is about 8–9 at μ ≈ 30–40, where k = 3 is at μ_eff ≈ 11–14. It is the route to μ > 35 if the fit holds.
- Tools: `../../structured/haar_sym` (built from haar_sym.c with `gcc -O3 -march=native -fopenmp`), THREADS=1, nice,
  timeout. Verifiers: `../../structured/tools/hcsl` and `hc2` (SL, > 20M), `haarcheck_psl` (PSL, > 20M), and
  `../../frontier/build_haar2.py` (≤ 20M). Built from the checked-in sources.

## Screens (RANDORB, 150 random symmetric S per group, cost statistics only)

All 142 groups with μ ≤ 36 (k = 5, f = 0, 67 groups) or 17 ≤ μ ≤ 26 (k = 3, f = 1, 75 groups) in N ∈ [30.0M, 34.0M].
Median random cost, the best few:

| k | group | N | μ | |Fix| | min | p1 | median |
|---|---|---|---|---|---|---|---|
| 3 | sl 163 × 7 | 30,314,088 | 17.3 | 161 | 3 | 5 | 22 |
| 3 | sl 89 × 43 | 30,309,840 | 17.2 | 89 | 3 | 6 | 23 |
| 3 | prod psl 3 × psl 73 × 13 | 30,337,632 | 17.5 | 107 | 4 | 5 | 28 |
| 3 | psl 97 × 67 | 30,571,296 | 19.7 | 47 | 6 | 9 | 30 |
| 3 | psl 73 × 157 | 30,532,104 | 19.3 | 35 | 9 | 12 | 33 |
| 3 | sl 73 × 79 | 30,726,576 | 21.2 | 71 | 11 | 12 | 34 |
| 5 | sl 79 × 61 (the record group, as a control) | 30,070,560 | 15.3 | 79 | 4 | 5 | 27 |
| 5 | psl 125 × 31 | 30,271,500 | 16.9 | 124 | 6 | 9 | 28 |
| 5 | psl 61 × 271 | 30,747,660 | 21.5 | 29 | 9 | 11 | 38 |
| 5 | prod psl 11 × psl 11 × 71 | 30,927,600 | 23.4 | 24 | 6 | 7 | 38 |
| 5 | psl 101 × 61 | 31,421,100 | 29.7 | 49 | 7 | 16 | 40 |
| 5 | sl 59 × 151 | 31,003,320 | 24.3 | 59 | 12 | 12 | 45 |
| 5 | psl 179 × 11 | 31,543,380 | 31.5 | 89 | 7 | 10 | 46 |

Reading: at these μ the k = 5 random costs are not clearly better than k = 3 (the control, sl 79 × 61 at k = 5, has
median 27 against 30 at k = 3). So the random-S screen does not settle it; the orbit search does.
Products (prod …) are not used for records above 20M: no low-memory checker exists for them.

## Searches launched (orbq.sh, 4 queues, THREADS=1)

Job files and logs: `../../structured/runs/raise-d10D10/` (`jobs_{a,b,c,d}.txt`, `queue_*.err`, one log per job).

- a: k = 3, f = 1, sl 163 × 7, μ 17.3, 1200 s (a cheap rung; would give 60,628,176 if solved)
- b: k = 5, f = 0, psl 101 × 61, μ 29.7, 3600 s (the main attempt above μ = 25)
- c: k = 5, f = 0, psl 61 × 271, μ 21.5, 1800 s
- d: k = 5, f = 0, sl 59 × 151, μ 24.3, 2400 s

## Status log

- 2026-10-25 07:20: started. Compiled haar_sym and the three checkers. Screens launched.
- 07:23–07:53: screens finished (see table). Queues a–d launched at 07:54.
