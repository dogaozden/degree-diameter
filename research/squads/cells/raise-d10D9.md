# Cell (Δ, D) = (10, 9): raise-d10D9 (Haiku worker)

Branch: claude/raise-d10d9-record-w585yh. Started 2026-10-25 (UTC session). Table value 7,057,400 (DS14v2); bipartite
Moore bound 96,855,122.

## Status

**New record: 8,362,560 vertices** = 2·|PSL(2,31) × Z281| (psl 31 x Z281, orbit k=5, m=2, f=0, μ = 39.0),
research/frontier/sols/d10D9_psl_31_281_orb5f0_s1.txt. build_haar2.py VALID (edge-list sha256
e02e5fb43ef1ad895d35c03ff92cdcd58a0f30a0782ecba861db2a5c46b4f33d), haarcheck_psl VALID. Found after 88,921 evaluations
(1,913 s, one thread). Log: research/structured/runs/d10D9_psl_31_281_orb5f0_s1.log.
It beats 8,334,480 (psl 41 x Z121, research/frontier/sols/d10D9_psl_41_121_orb5f0_s2.txt) by 28,080 (+0.3 %).

Window for the next record: N > 4,181,280 (2N > 8,362,560).

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
- 08:00–08:20 UTC: four runs on the next window (k=5 f=0 on psl 29 x Z341, psl 41 x Z121; k=3 f=1 on sl 25 x Z259 and
  pgl 25 x Z259, all N ≤ 4.04M except psl 41). psl 29 x Z341 (k=5) solved at 206,057 evaluations: 8,306,760 vertices.
  The k=3 runs on N = 4,040,400 were stopped as obsolete (below the new bar). Best costs at 19 min: psl 41 x Z121 (k=5)
  4, psl 29 x Z341 10 (solved later), pgl 25 x Z259 12, sl 25 x Z259 24.
- Still running: psl 41 x Z121 (k=5 f=0, N = 4,167,240; the only candidate above 8,306,760 in this window).
- 08:26–08:40 UTC: psl 41 x Z121 (k=5 f=0) solved on seed 2 at 131,481 evaluations: 8,334,480 vertices. Seed 1 (best 4)
  was stopped as obsolete. Still running: psl 31 x Z281 (k=5 f=0, N = 4,181,280, best 21 at 5 min). sl 23 x Z343 (k=3,
  N = 4,165,392, best 54) is below the new bar and was stopped.
- 08:50 UTC: psl 31 x Z281 (k=5 f=0, μ 39.0) solved on its first seed at 88,921 evaluations: 8,362,560 vertices.
  Stopped as obsolete: psl 49 x Z71 (N = 4,174,800, best 6), psl 29 x Z343 (k=3, N = 4,177,740, best 30), prod psl 5 psl 9 x Z193
  (k=3, N = 4,168,800, best 38).
