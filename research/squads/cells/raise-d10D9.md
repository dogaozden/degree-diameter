# Cell (Δ, D) = (10, 9): raise-d10D9 (Haiku worker)

Branch: claude/raise-d10d9-record-w585yh. Started 2026-10-25 (UTC session). Table value 7,057,400 (DS14v2); bipartite
Moore bound 96,855,122.

## Status

**New record this session: 8,064,960 vertices** = 2·|PSL(2,31) × Z271| (psl 31 x Z271, orbit k=5, m=2, f=0, μ = 24.5),
research/frontier/sols/d10D9_psl_31_271_orb5f0_s1.txt. build_haar2.py VALID (edge-list sha256
3f69f5a0db8f9d53b6d25506c51db2970bfb8884cca5a052b50af077c92b7871), haarcheck_psl VALID, found in 4,545 evaluations (96 s).
It beats the previous record 8,003,856 (sl 83 x Z7, k=3 m=3 f=1, research/frontier/sols/d10D9_sl_83_7_orb3_s1.txt)
by 61,104 (+0.76 %). Log: research/structured/runs/d10D9_psl_31_271_orb5f0_s1.log.

Window for the next record: N > 4,032,480 (2N > 8,064,960).

## Method

Orbit search of research/structured (haar_sym, ORBIT="3 3 1", FAST=2 wide rows where a cyclic subgroup of order
≥ 64 exists, otherwise haar_gen3's evaluator). Queues via tools/orbq.sh, THREADS=1, one run per core, up to 4 at a
time. Solutions are checked with ../frontier/build_haar2.py (up to 20M vertices).

Window: a new record needs N = |G| > 4,001,928, i.e. 2N > 8,003,856. From SIZE_LAW (mu_plan.py) μ = 25 sits at
2N ≈ 8.08M and μ = 23.5 at 2N ≈ 8.04M.

Candidates (k = 3, m = 3, f = 1, from orb_screen --list, N = |G|, μ):
- sl 23 x Z331, N = 4,019,664, μ 23.5 (no cyclic subgroup of order ≥ 64: haar_gen3 evaluator, slower)
- psl 29 x Z331, N = 4,031,580, μ 24.5
- psl 31 x Z271, N = 4,032,480, μ 24.5
- sl 25 x Z259, N = 4,040,400, μ 25.2 (and pgl 25 x Z259 same N)
- pgl 23 x Z331 (same N as sl 23 x Z331)

Screen: `orb_screen.py 10 9 4001929 4060000 "3 3 1" --fams sl,psl,pgl --samples 1500` (log in the scratchpad).

## Log

(see below, newest last)

### 2026-10-25 07:42–07:55 UTC (session start)

- Built haar_sym from research/structured/haar_sym.c (gcc -O3 -march=native -fopenmp), THREADS=1 per run.
- Screen (orb_screen, 1,500 RANDORB samples per group, k = 3, m = 3, f = 1). Lower-tail costs (min / p1 / p10 / median):
  - record group pgl 83 x Z7 (μ 22.2, baseline): 36 / 56 / 77 / 126
  - pgl 25 x Z259 (μ 25.2): 32 / 72 / 116 / 231
  - psl 31 x Z271 (μ 24.5): 33 / 59 / 98 / 180
  - psl 29 x Z331 (μ 24.5): 54 / 71 / 108 / 200
  - sl 23 x Z331 (μ 23.5): 72 / 100 / 150 / 250 (also pgl 23 x Z331: 42 / 75 / 123 / 250)
  - sl 25 x Z259 (μ 25.2): 66 / 84 / 128 / 224
- Annealing, one seed each, 3,600 s budget (orbq.sh queues, sequential seeds 1 and 2 per group):
  - psl 29 x Z331, k=3 m=3 f=1: cost 18 at 330 s (16,000 evals), still running
  - psl 31 x Z271, k=3 m=3 f=1: cost 18 at 330 s, still running
  - sl 23 x Z331, k=3 m=3 f=1: cost 38 at 330 s, still running (no cyclic subgroup of order ≥ 64: slower evaluator)
  - psl 31 x Z271, k=5 m=2 f=0 (order-5 automorphism exists since 31 ≡ 1 mod 5, 271 ≡ 1 mod 5): cost 10 at 30 s
- Not yet solved. Next: more seeds, and the k=5 f=0 structure on the other groups with q ≡ ±1 mod 5 (psl 29 x Z331).
