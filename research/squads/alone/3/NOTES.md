# squad-alone-3: Haar graphs of metacyclic and affine groups, Δ = 16, D = 5

Haiku worker, job "squad-alone-3", 2026-10-24 (about 2 h of compute, THREADS ≤ 4 at all times).
Goal: a bipartite graph of max degree 16 and diameter 5 with more than 31,460 vertices, i.e. a Haar graph
H(G,S) with |S| = 16 and |G| ≥ 15,731 (2|G| vertices).

## Result

No graph beyond the goal. The region tops out well below it:

- **Best order reached in the region with cost 0:** Z_421 ⋊_r Z_21 (N = 8,841), a valid 16-regular diameter-5
  graph on **17,682 vertices** (`sols/wall1_00_meta_421_21_286_n1.txt`, edge list
  `meta_421_21_N8841.edges.txt.gz`, check `check_meta_421_21_N8841.txt`, build_haar2.py VALID, sha256
  4229dcb9fd8f84e4714b7bbfd21d07da821d8c7c90f67cbf9d948521d9f51f27). Not a record: the table has 27,300.
- **At the target order (N ≥ 15,731):** best cost 520 uncovered (Z_757 ⋊ Z_21, N = 15,897), never 0.

## Why (the lemma and the count)

For a Haar graph with |S| = 16 and D = 5: diameter ≤ 5 iff (S⁻¹S)² = G = (SS⁻¹)² (research/d5/REPORT.md lemma).
The word count is W = 1 + 16·15 + 16·15³ = 54,241. At N = 15,731 a random-like S leaves
μ = N·e^(−W/N) ≈ 500 elements uncovered per side. The annealer cannot close that gap.

The first-moment ceiling for random-like S (solve N·e^(−W/N) = Δ·ln N, research/frontier/SIZE_LAW.md) is
N ≈ 12,300, i.e. about 24,600 vertices. That is below both the table value 27,300 (N = 13,650) and the target.

## What was run

All with `research/frontier/haar_gen3.c` (compiled `gcc -O3 -march=native -fopenmp`), d = 16, D = 5, K = 4 candidate
moves per step. Costs are uncovered elements summed over both sides (0 = valid). The scoreboard holds one JSON line
per attempt (`scoreboard.jsonl`).

1. **Calibration (90 s, 2 threads).** Z_1009 ⋊ Z_8 (N = 8,072): cost 29. Z_1009 ⋊ Z_16 (N = 16,144): cost 868.
2. **Sweep (60 s, 1 thread each, 24 configs, N ∈ [15,768, 16,551]).** Families: AGL(1,q) × Z_n for q ∈ {16, 25, 32,
   37, 41, 49, 64, 73, 127, 128}; metacyclic Z_p ⋊ Z_k with p prime, k ∈ {2 … 48}, with and without a Z_n factor.
   Best costs: metacyclic with k ≥ 12 (520 to 949; best Z_757 ⋊ Z_21 at 520); AGL (559 to 685; best AGL(1,73) × Z_3 at 559);
   k ∈ {2, 3, 4, 5} or with a Z_n factor were much worse (776 to 3,122).
3. **Plateau check (600 s, 2 threads each).** Z_757 ⋊ Z_21: 530 (no gain on the 60 s run). AGL(1,73) × Z_3: 521 (from 559).
   The cost stays near 520 with more time, so the floor is structural, not a run-length artifact.
4. **Wall (240 s, 1 thread).** Z_421 ⋊ Z_21 (N = 8,841): **cost 0** (valid). Z_463 ⋊ Z_21 (N = 9,723): cost 2.
   Z_433 ⋊ Z_24 (N = 10,392): 44. Z_547 ⋊ Z_21 (N = 11,487): 44.

So the empirical wall for metacyclic Haar graphs at Δ = 16, D = 5 is N ≈ 9,000–9,500 (about 18,000–19,000 vertices).
That sits at about 0.73 of the heuristic first-moment ceiling (about 12,300). The D = 5 records in SIZE_LAW.md reach 0.94 of N_h at smaller Δ.

## Calibration against the D = 5 records

The records in research/d5/REPORT.md sit at N/W ≈ 0.31 (Δ = 8, AGL(1,7) × Z_21), 0.28 (Δ = 9), and about 0.27 (Δ = 10
near misses). At Δ = 16 the wall is N/W = 8,841 / 54,241 ≈ 0.16. The goal needs N/W ≈ 0.29. The ratio falls with Δ,
so the Δ = 16 target is not in reach by extrapolation.

## What I did not try, and why

- **Symmetric S (orbits under an automorphism)**, from research/structured on claude/structured-search-orbit-w5dd4f.
  Its STRUCTURE.md §1 and §8 say symmetric S shares the same first-moment ceiling as random S. It also says D = 5 with
  Δ ≥ 13 lies above that ceiling. Δ = 16 is in that class, so I did not spend compute on it.
- **Non-metacyclic, non-affine groups.** Other workers' regions.
- **Multiple seeds, longer runs at N = 9,723 (cost 2).** A valid 19,446-vertex graph would not beat the table or the goal,
  so I left it.

## What would change the answer

Covers with negatively correlated words (algebraic structure, e.g. voltage lifts over generalized polygons or
structured bases) can beat the random-like ceiling. That is a different construction family, not Haar graphs over
these groups.

## Files

- `scoreboard.jsonl`: one line per attempt (32 lines).
- `sols/`: the one valid solution file.
- `logs/`: stdout of the sweep runs and calibration runs.
- `tools/mc.py`, `tools/sweep.py`: group-parameter helper (prime Z_p ⋊ Z_k) and the parallel sweep driver
  (env `BIN`, `SECS`, `TAG`).
- `meta_421_21_N8841.edges.txt.gz`, `check_meta_421_21_N8841.txt`: the verified 17,682-vertex graph and its check.
