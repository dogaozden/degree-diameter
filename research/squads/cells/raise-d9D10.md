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
