# haar_fast: where haar_gen3's time goes, what was changed, measured factors

structured-search job (Opus), 2026-10-23. Machine: cloud container, Intel Xeon (Cascade Lake) 2.8 GHz, 4 cores,
L2 1 MB/core, L3 33 MB, AVX-512. Compiler: gcc 13.3 `-O3 -march=native -fopenmp`. Baseline: the unmodified
`research/frontier/haar_gen3.c`. Program: `haar_fast.c` (see README for flags).

## 0. Result: clean measurement on an idle machine

`tools/speed_bench.sh` ran alone on the box (load 0.7 at the start; 22:13–22:43), one process at a time,
single thread. Both binaries were built from the committed sources (`../frontier/haar_gen3.c` unmodified,
`haar_fast.c`). Raw output: `runs/speed_bench_clean.txt`. Table: `tools/speed_table.py`.

| cell, group | N | same RANDSAMPLE costs | ms/eval FAST=0 → 2 | E2E steps | E2E s FAST=0 → 2 | E2E factor | same trajectory hash | haar_gen3 evals/s | haar_fast evals/s | factor |
|---|---|---|---|---|---|---|---|---|---|---|
| (7,8) psl 17 × Z18 | 44,064 | yes | 0.0404 → 0.0595 (0.68×) | 100000 | 38.6 → 28.7 | **1.34** | yes | 24,235 | 28,947 | 1.19 |
| (6,7) meta 279 15 7 × Z1 | 4,185 | yes | 0.0091 → 0.0104 (0.88×) | 20000 | 1.3 → 1.3 | **0.99** | yes | 120,592 | 122,400 | 1.01 |
| (8,9) sl 59 × Z3 | 615,960 | yes | 1.28 → 0.938 (1.36×) | 4000 | 39.8 → 27.6 | **1.44** | yes | 744 | 1,160 | 1.56 |
| (7,10) sl 49 × Z9 | 1,058,400 | yes | 1.64 → 0.941 (1.74×) | 1500 | 22.6 → 8.3 | **2.73** | yes | 539 | 1,484 | 2.75 |
| (8,10) sl 107 × Z3 | 3,674,808 | yes | 10.1 → 2.64 (3.81×) | 600 | 46.0 → 14.8 | **3.10** | yes | 106 | 356 | 3.36 |
| (15,8) sl 101 × Z8 | 8,241,600 | yes | 35.8 → 15.1 (2.38×) | 150 | 41.9 → 18.0 | **2.33** | yes | 27.2 | 68.4 | 2.52 |
| (10,8) psl 23 × Z97 | 588,984 | yes | 1.33 → 0.527 (2.53×) | 800 | 9.0 → 2.8 | **3.22** | yes | 747 | 2,269 | 3.04 |
| (12,9) sl 127 × Z8 | 16,386,048 | yes | 120 → 39.4 (3.05×) | 40 | 35.6 → 11.4 | **3.12** | yes | 8.44 | 27.5 | 3.26 |
| (10,10) sl 307 × Z1 | 28,934,136 | yes | 199 → 76.4 (2.60×) | 25 | 38.0 → 15.5 | **2.44** | yes | 5.39 | 13.2 | 2.45 |

Columns:
- **same RANDSAMPLE costs**: haar_gen3 and haar_fast print the identical quantile line for 200 random S.
- **ms/eval**: `BENCH` (single-generator replacements, no abort), haar_gen3's evaluation code (FAST=0) against wide
  rows (FAST=2).
- **E2E**: the same annealing run (same seed, `VCLOCK`, `MAXSTEPS`) with FAST=0 and FAST=2. Both print the same
  `TRACE` hash, so the trajectory and every cost are identical; the factor is the wall-time ratio. **This is the
  speedup at bit-identical results.**
- **evals/s**: haar_gen3 itself against haar_fast, 60 s runs with the normal wall-clock schedule (the trajectories
  differ there, because the schedule follows the clock).

Reading:
- **Small groups (N ≲ 5·10⁴): 1.0–1.3×.** Everything fits in L2. A wide-row evaluation is even slower there (BENCH
  0.68–0.88×), and the exact abort wins it back.
- **N ≈ 0.6–1·10⁶: 1.4–3.2× end to end** (1.6–3.0× in evaluations per second). The spread comes from the cell more
  than from N: (8,9) has two BFS per evaluation and short dense levels.
- **N ≥ 3.7·10⁶: 2.3–3.1× end to end** (2.5–3.4× in evaluations per second).

All nine cells: same costs and same trajectory hash.

## 1. Profile of haar_gen3 (per candidate evaluation, single thread)

`BENCH=m` evaluates m single-generator replacements of a random S and times the table build and every BFS level.
FAST=0 is haar_gen3's own evaluation code inside haar_fast (identical results).

| cell, group | N | nH | ms/eval | tables | dense BFS levels (ms each) |
|---|---|---|---|---|---|
| (7,8) psl 17 × Z18 | 44,064 | 51 | 0.040 | 0.007 (17 %) | 0.009, 0.009, 0.008 |
| (8,9) sl 59 × Z3 | 615,960 | 60 | 1.25 | 0.33 (26 %) | 0.13, 0.24, 0.24, 0.23 (two BFS) |
| (8,10) sl 107 × Z3 | 3,674,808 | 54 | 7.7 | 3.9 (51 %) | 0.6, 0.7, 1.0, 1.1, 1.0 |
| (15,8) sl 101 × Z8 | 8,241,600 | 51 | 32.7 | 7.9 (24 %) | 2.4, 5.5, 8.4, 8.5 |

Findings:
1. **Table building is 17–51 % of an evaluation.** Each of the R = N/nH rows needs one matrix product and two random
   lookups (the q³-entry key table, then the N-entry coset table). At q = 107 both tables are far larger than L2.
2. **The dense BFS levels are memory-latency bound.** About 3–4 ns per (row, generator) operation once the bitsets
   pass L2 (N ≳ 10⁶), i.e. one random 64-bit read-modify-write per 51–60 useful bits. Arithmetic is negligible.
3. **The last level is ~1/3 of the BFS**, and two thirds of the candidates of a move cannot win (measured: 67 % are
   abandoned by the exact rule below).

## 2. What was tried, and what each change is worth

All changes keep the cost of every S identical (checked by RANDSAMPLE on 9 group families and by trajectory hashes,
§3).

| change | idea | effect |
|---|---|---|
| pull instead of push | dense levels gather from the inverse tables instead of scattering | **none** (0.9–1.1×): still one random access per 64-bit word |
| counting last level, row-full exit | stop ORing sources into a target row once it is full; count uncovered on the fly | last level 1.1–1.3× faster |
| exact early abort | abandon a candidate once its partial uncovered count ≥ the best earlier candidate's cost (strict in multi-thread mode) | 67 % of candidates abandoned; ~1.1–1.2× end to end (only the last level is saved) |
| 512-bit rows via lane permutes | cosets of a cyclic subgroup of order ≤ 512, AVX-512 rotation | 1.6–1.7× at N ≥ 4M but **slower** below: 4 permutes per rotation saturate port 5 (~17 cycles) |
| **doubled 256-bit rows** | rows of a cyclic subgroup of order 64–256, frontier stored as v ∥ v (one 64-byte line), rotation = window read (two loads, two variable shifts) | dense levels 2–4× faster at N ≥ 10⁶; tables need N/nHW products (4× fewer) |
| software prefetch (8 rows ahead) | prefetch the source lines of later rows | ≤ 10 % in the real code (large in a microbenchmark at N = 3·10⁷: 3×) |
| block-pipelined table build | compute 32 keys, prefetch, then the coset lookups | tables 7.9 → 1.1 ms at (15,8) together with the 4× fewer rows |

Microbenchmark (`/tmp` scratch, 15 generators, random tables), ns per element-generator for one dense level:

| N | 64-bit rows | 64-bit + prefetch | doubled 256-bit | doubled 256-bit + prefetch |
|---|---|---|---|---|
| 6·10⁵ | 0.020–0.032 | 0.034 | 0.009 | 0.010 |
| 8·10⁶ | 0.050–0.096 | 0.072 | 0.017–0.042 | 0.012 |
| 3·10⁷ | 0.067–0.11 | 0.084 | 0.065–0.089 | 0.021 |

(Ranges: repeated runs on a shared VM; the timer noise is ±30 %.)

Analysed and not implemented, with the reason:
- **Incremental cost update when one generator changes.** Words avoiding the replaced generator are a fraction
  ≈ ((Δ−2)/(Δ−1))^(D−2)·(Δ−1)/Δ of all words: 60 % at (15,8), 26 % at (8,10). The elements left uncovered without
  that generator, U_i, number N·e^(−0.6λ) ≈ 3·10⁻⁴ N at (15,8) and 2 % at (8,10). An exact update must still recompute
  levels D−3 and D−2 for all words through the new generator, and those levels are dense. So it saves at most the
  last level, which the row-full exit and the abort already make cheap. A one-occurrence filter (words with a
  single use of the new generator, checked by meet-in-the-middle on U_i) costs |U_i|·(Δ−1)^((D−2)/2) ≈ 10⁷ lookups at
  (15,8), the same as a BFS, and is not exact (≈10 % of the new words use the generator twice).
- **Meet-in-the-middle covering.** x is covered iff Ball_a(e) ∩ x·Ball_b⁻¹ ≠ ∅. Testing all N elements costs
  N·|Ball_b| ≫ N·Δ·(levels). It is useful only for a handful of targets, which is how the targeted moves already work.
- **Arithmetic coset indexing (torus/Bruhat structure)** to replace the two random lookups in the table build. After
  the 4× fewer rows and the prefetch pipeline the tables are 8–15 % of an evaluation, so this would gain ≤ 1.15×.

## 3. Bit-identity

1. **Same costs.** For 8 groups (psl 17 × Z18, sl 59 × Z3, sl 11, meta 279 15 7, prod psl 5 psl 9 × Z5,
   sl 49 poly × Z9, sl 101 × Z8, pgl 61), `RANDSAMPLE` prints identical cost quantiles from haar_gen3 and
   haar_fast (same random S, same costs). The clean benchmark (top table) repeats this on every cell it times.
2. **Same trajectory.** With `VCLOCK` (a deterministic annealing clock) and `MAXSTEPS`, FAST=0 (haar_gen3's
   evaluation), FAST=1 and FAST=2 runs with the same seed print the same `TRACE` hash: a hash of the move slot,
   chosen candidate, its cost, the acceptance and the current cost at every step. This holds on all cells in the
   table below, and also with `THREADS=2` and `THREADS=4` (sl 59 × Z3, 1,500 steps: all four hashes 9bf129c2…). The wide-row mode rebuilds the uncovered lists in haar_gen3's own coset order (sorting, or replaying
   the reservoir when > 65,536 are uncovered), so even the targeted moves draw the same elements.
3. Every solution found by haar_fast or haar_sym passes haar_gen3's own full diameter check and build_haar2.py.

## 4. End-to-end factors (same seed, same trajectory, wall time ratio)

Same seed, `VCLOCK`, `MAXSTEPS`; FAST=0 is haar_gen3's evaluation code, FAST=2 the default. These preliminary
numbers were measured while 1–3 other search jobs ran on the box (shared L3 and memory bandwidth). The clean
measurement is §0.

| cell, group | N | steps | FAST=0 (s) | FAST=2 (s) | factor | hashes equal |
|---|---|---|---|---|---|---|
| (7,8) psl 17 × Z18 | 44,064 | 100,000 | 34.2 | 28.5 | 1.20 | yes |
| (6,7) meta 279 15 7 | 4,185 | 20,000 | 1.27 | 1.26 | 1.01 | yes |
| (9,5) sl 11 | 1,320 | 20,000 | 0.71 | 0.92 (64-bit FAST=1 path; now falls back to FAST=0) | 0.77 → 1.0 | yes |
| (8,9) sl 59 × Z3 | 615,960 | 4,000 | 43.7 | 28.0 | 1.56 | yes |
| (8,10) sl 107 × Z3 | 3,674,808 | 600 | 44.3 | 13.9 | 3.19 | yes |
| (15,8) sl 101 × Z8 | 8,241,600 | 150 | 23.0 | 9.8 | 2.36 | yes |
| (12,9) sl 127 × Z8 | 16,386,048 | 40 | 38.5 | 12.1 | 3.19 | yes |

Groups without a cyclic subgroup of order ≥ 64 (small groups, PGL(2,61), products like A5 × A6 × Z5, or Q × Z_p with
a large prime p) use haar_gen3's evaluation unchanged, so they are never slower.

## 5. What this buys

SIZE_LAW §4.1: each 10× in evaluations adds about 4.6 to the reachable μ, i.e. about 3–4 % in N. The 1.0–3.2× here
is worth about 0.5–1.5 % in N at the walls. Running the 4 cores as 4 seeds multiplies throughput by 4 again (the
K candidates of a move can also be split over threads, `THREADS=t`, with the abort made strict so results stay
identical). These are honest constant factors: the structure of the bitset BFS is already close to the memory system's
limits (~0.01–0.02 ns per element-generator in the best microbenchmark, against 0.03–0.07 now in the real code). The
remaining headroom is a factor of 2–3 on a CPU. A GPU (random 64-byte reads at ~1 TB/s) might give another 10–30×.
None of this approaches 10⁹. See STRUCTURE.md §6 for what does change the exponent.
