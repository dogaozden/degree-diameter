# research/structured: faster and structured Haar search

Job "structured-search" (2026-10-23, cloud session). Goal: get past the random-search wall of the Haar graph search
(`../frontier/haar_gen3.c`, `../frontier/SIZE_LAW.md`) by
(A) raw speed, keeping every cost bit-identical, and
(B) structured generator sets S that change the exponent, not just the constant.

- `SPEEDUP.md`: what was profiled, what was changed, and the measured factors against haar_gen3 on identical seeds.
- `STRUCTURE.md`: the structured families (orbit-symmetric S under an automorphism, Heisenberg groups, metacyclic
  scalings, …), what each found, the negative results, and the honest answer to "can it be made a billion times
  more efficient?".

## Programs

Build (x86-64 with AVX2 and AVX-512F/VL, e.g. this container's Cascade Lake; gcc 13):

```
gcc -O3 -march=native -fopenmp -o haar_fast haar_fast.c -lm
gcc -O3 -march=native -fopenmp -o haar_sym  haar_sym.c  -lm
```

### haar_fast.c: drop-in replacement for haar_gen3

Same command line, RESULT line and solution files as haar_gen3 (`d D seconds seed K outfile GROUP... n`). It computes
the same cost for every S and, given the same seed and a deterministic clock, follows the same search trajectory.
Only the evaluation is faster:

- dense BFS levels are pulls (gathers through the inverse tables) instead of scatters;
- the last BFS level only counts: a target row stops as soon as it is full;
- best-of-K: a candidate is abandoned as soon as its partial count proves it cannot be selected (exact);
- **wide rows** (default): cosets of a cyclic subgroup of order 64..256, each row a 256-bit vector stored twice (one
  64-byte cache line), so a rotation is a window read; tables need N/nHW products instead of N/nH; software
  prefetch. Groups without a cyclic subgroup of order >= 64 fall back to haar_gen3's own evaluation code.

Extra environment variables (all optional):

| var | meaning |
|---|---|
| `FAST=0/1/2` | 0: haar_gen3's evaluation code; 1: 64-bit rows with pull/abort; 2 (default): wide rows |
| `ABORT=0` | disable the exact early abort |
| `VCLOCK=x` | the annealing schedule uses x seconds per step instead of the wall clock (deterministic runs) |
| `MAXSTEPS=n` | stop after n annealing steps |
| `TRACE=1` | print `TRACE steps=… hash=…`: a hash of every step (slot, candidate, cost, accept) |
| `BENCH=m` | time m single-generator evaluations: ms/eval, table time, time per BFS level |
| `HWMIN`, `HWMAX`, `PFD` | wide-row subgroup order range (default 64..256), prefetch distance (default 8) |

`THREADS`, `RANDSAMPLE`, `PROFILE`, `COOL`, `REHEAT`, … behave as in haar_gen3.

Memory: wide mode keeps haar_gen3's coset index (4N bytes, needed to reproduce its uncovered lists exactly) and
adds its own (4N bytes). That is about 18 instead of 14 bytes per group element, e.g. 2.9 GB instead of 2.3 GB at
N = 158M. Use `FAST=0` when memory is the limit. When more than 65,536 elements are uncovered, rebuilding
haar_gen3's reservoir sample costs O(N) group products. That happens only for hopeless S and the trajectory stays
exact.

Identity test (both lines must show the same hash):
```
TRACE=1 VCLOCK=0.01 MAXSTEPS=4000 FAST=0 ./haar_fast 8 9 3600 1 8 /dev/null sl 59 3
TRACE=1 VCLOCK=0.01 MAXSTEPS=4000 FAST=2 ./haar_fast 8 9 3600 1 8 /dev/null sl 59 3
```

### haar_sym.c: structured (automorphism-invariant) search

haar_fast plus:

- `ORBIT="k m f"`: S = {e} ∪ (f−1 generators fixed by α) ∪ (m orbits of size k), with d = f + k·m. α is chosen
  automatically: conjugation by an element of the base group Q (order k on Q) times z ↦ r·z on Z_n, with r of
  order k and as few fixed z as possible. For `meta` groups a scaling (a, j) ↦ (u·a, j) is tried first. For `heis` it
  is the scaling (x, y, z) ↦ (a x, b y, ab z). Annealing moves replace a whole orbit (or one fixed generator). The
  energy is uncovered/k and targeted moves avoid the orbit being replaced. Override with `ALPHA=<index>|e`, `AR=<r>`,
  `AMU=<u>`, `AHA=<a> AHB=<b>`.
- `RANDORB=m` (with `ORBIT`): cost statistics of m random symmetric S, plus a histogram of cost/k (screening).
- `RESTART=1` (with `ORBIT`): a reheat starts from fresh random orbits instead of the best S found so far.
- `AFROB=j` (with `ORBIT`, matrix groups over GF(p^e)): α = the field automorphism x ↦ x^(p^j) on the entries.
  This is the "field structure" experiment; it does worse than conjugation (STRUCTURE.md §5).
- `LEVELS=n` (with `RANDSAMPLE` or `RANDORB`): ball sizes per BFS level for the first n samples.
- group family `heis q`: 3×3 upper unitriangular matrices over GF(q).

Solution files have the haar_gen3 format (first generator e), so `../frontier/build_haar2.py` checks them.

Example (Δ7·D8 record, 0.2–15 s):
```
ORBIT="3 2 1" ./haar_sym 7 8 300 1 8 sol.txt psl 19 14
python3 ../frontier/build_haar2.py sol.txt
```

### tools/

- `orb_screen.py d D LO HI "k m f"`: lists Q × Z_n in an order window (n with all prime factors ≡ 1 mod k, unless
  `--anyn`), runs RANDORB on each and ranks them by the lower tail of the cost.
- `orbq.sh JOBFILE OUTDIR`: sequential job queue (`k m f | d D secs seed K GROUP... n` per line); every solution is
  re-checked with build_haar2.py and the verdict is appended to the log.
- `mu_plan.py`: per cell, μ = N e^(−W/N) at the table value and at our best, and the orders where μ reaches given
  levels.
- `cmp.sh SECS < list` and `cmp_table.py LOG`: head-to-head of random-S annealing (haar_fast) against orbit annealing
  (haar_sym) on the same groups, seeds and wall-clock budget, as a markdown table.
- `speed_bench.sh H3 HF`: the measurements behind SPEEDUP.md (RANDSAMPLE identity, BENCH breakdowns, end-to-end
  trajectory hashes and wall-time ratios, haar_gen3 vs haar_fast evaluations per second).

`runs/` has the logs and build_haar2 outputs of the record runs. New solution files are in `../frontier/sols/`
(names contain `orb3`).
