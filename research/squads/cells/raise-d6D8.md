# Cell (Δ, D) = (6, 8), bipartite: raise attempt, round 2 (job "raise2-6-8", branch claude/raise2-6-8-haar-n4stxc)

## Status
- Record held: **31,680 vertices** (2·N, N = 15,840, Haar graph of PSL(2,11) × Z24, ORBIT "2 3 0",
  `research/frontier/sols/d6D8_psl_11_24_orb2f0_s1.txt`). Table value 29,790; Moore bound 195,312.
- This round: **no improvement**. No cost-0 set found for any group with N ≥ 15,841. Verdict and reasons below.
  Notes and evidence: `research/squads/raise2-d6D8/NOTES.md`; logs in `research/squads/raise2-d6D8/runs/`;
  screens in `research/squads/raise2-d6D8/screen/`.

## Correction to round 1
Round 1 wrote that heisenberg and metacyclic groups "need new code". They do not: `research/structured/haar_sym.c`
parses `meta m k r`, `heis q`, `agl1 q` (and `prod`, `csl`, `tpgl`; the last two are plain-only, ORBIT refuses them).

## What was run (ORBIT mode, THREADS=1 per run, timed; all Haar graphs H(G, S) with |S| = 6)
| wave | orbit type | groups (N) | time | best cost (uncovered) |
|---|---|---|---|---|
| 1 (round 2) | k=2, "2 3 0" | meta 1223×13 r117 (15899), meta 1223×13 r236 (15899), meta 953×17 r16 (16201), meta 1453×11 r69 (15983) | 240–258 s, stopped/finished | 11, 11, 12, 18 |
| 2 (round 2) | k=3, "3 2 0" | psl 7×Z95 (15960) ×2 seeds, psl 7×Z98 (16464), sl 7×Z49 (16464) | 900 s each | 11, 11, 6, 3 |
| 3 (round 2) | k=3, "3 2 0", ALPHA=120/265/141/170 | sl 7×Z49 (16464) | 900 s each | 3, 3, 3, 3 |

Random-sample screens (haar_sym RANDORB, 2000 samples per group; metric (p1 + p10)/2 of the cost, control
psl 11×Z24 at N = 15,840 scores 48):
- k=2, "2 3 0": all sl/psl/pgl × Z_n, agl1 × Z_n, heis × Z_n and metacyclic meta m k r with k ≤ 60, N = 15,841..16,290
  (3,739 specs, `screen/k2_full.tsv`). Best scores: metacyclic 51–52 (N 15,899); all sl/psl/pgl with k=2 are
  170–600; heis and agl1 are 570+. N = 16,290..17,000 base families screened (`screen/k2_tail_base.tsv`); the metacyclic
  part of that tail (k ≤ 12 and up) was not screened at k=2 (too slow at 30 specs/min).
- k=3, "3 2 0": all base families for N = 15,841..17,000 (207 specs, `screen/k3_base.tsv`) and all metacyclic
  specs with k ≤ 12 (5,336 specs, `screen/k3_meta_k12.tsv`; 1,078 have no order-3 automorphism). Best: psl 7×Z95 score 50.5,
  sl 7×Z49 score 51.0, psl 7×Z98 score 63.5; all metacyclic 368+.

Compute: about 2.5 core-hours of annealing (12 runs, 4 at a time, 240–900 s each) and about 3 core-hours of screening
(roughly 10,000 groups × 2,000–5,000 random samples per orbit type).

## Why the window does not open with these methods
- **Metacyclic groups** (which the k=2 screen liked best) do badly under annealing: best 11–18 after 1.4–2.4M evals,
  against 2.7M evals for the control's solve. Their evaluator also runs at ~8k evals/s (no cyclic subgroup of order
  ≥ 64, so the generic path), versus ~60k for the bitset path.
- **PSL(2,7) × Z_n with k=3** is the only family with competitive screen scores. Its best plateau is 3 (sl 7×Z49,
  N = 16,464 = 32,928 vertices if solved), reached by four different order-3 automorphisms and the default one, each
  after 55M evaluations. The repeated floor at 3 suggests a structural obstruction, not a bad α. Not verified (a diagnostic
  would print the uncovered set at the plateau, and I did not build one).
- **Order-3 automorphisms need a prime 1 mod 3 in Z_n** (or 9 | n): orders such as 96, 99 and 100 in the window are
  degenerate for k=3 (cost 12,000+). The usable k=3 orders are few.
- **Counting is optimistic.** The random model (expected cost-0 orbit sets ≈ options · e^{−μ/k}) predicted about 100 and
  about 7 solutions for psl 7×Z95 and sl 7×Z49, and thousands for k=2 at N = 15,840. The annealing does not see them.
  The model assumes independence that these groups do not have.
- **Alpha sweeps.** The tool does not reject an invalid ALPHA: it prints "alpha^k != 1" and carries on, so an unfiltered
  sweep is meaningless. Valid α for k=3 are the x in SL(2,7) with x³ = ±I (112 of 336; `alpha_valid.py`).

## What is not tried (and what I would try next)
1. **Two-orbit bi-Cayley lifts** (base graph with 2 vertices per side, degree 6, voltages in G): V = 4·|G|. A lift with
   |G| ≥ 7,921 beats the record, which opens groups of order 7,921..8,125 (e.g. PSL(2,8)×Z16 = 8,064, PGL(2,7)×Z24,
   A5×Z135, PSL(2,16)×Z2) that no Haar window covers. Its uncovered-count μ is about the same as the Haar graph at
   N = |G|·2 (μ ≈ 33 at |G| = 7,921, ≈ 38 at 8,064). It needs a new evaluator and annealer (BFS from 4 roots, bitset or
   group-table form); `research/squads/...` has no generic voltage-lift annealer on any branch I checked, only builders
   (`research/lifts/coordinator_check/build.py`) and checkers.
2. A diagnostic of the uncovered set at the sl 7×Z49 floor (is the cost-3 set one α-orbit, or a fixed set such as the
   lifts of −I?). It decides whether 3 is a hard floor for this group.
3. Metacyclic k=2 screen for N = 16,290..17,000 with k = 13..60 (not run). Low prior: the metacyclic k=2 screens did not
   predict annealing results.

## Verdict
No record raised. I am fairly confident these methods (Haar graphs with k = 2 or 3 orbits, and metacyclic, Heisenberg,
AGL(1), or PSL/SL/PGL base groups in N = 15,841..17,000) will not move the (6,8) cell past 31,680: every candidate
plateaus at cost ≥ 3, and the closest (sl 7×Z49, cost 3) stays put across four automorphisms. The untried route
(1) above needs new code and is the one to give a stronger worker. I'd rank it below the Haar work only because its
μ is a little higher.
