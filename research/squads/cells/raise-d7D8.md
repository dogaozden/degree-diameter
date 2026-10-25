# Cell (Δ, D) = (7, 8): raise the record (job raise-7-8)

Worker session on branch `claude/raise-d7d8-record-2irp7i`, started 2026-10-25 (UTC). Goal: beat our own record
**95,760** vertices (psl 19 × Z14, N = 47,880, 7-regular Haar graph, orbit search k = 3, m = 2, f = 1, found in
research/structured by claude/structured-haar-search-ws7bet). Table value 80,940. Moore bound 671,846.

## Status (update at every push)

- Baseline reproduced on this box: `ORBIT="3 2 1" haar_sym 7 8 120 1 8 … psl 19 14` → cost 0 after 255,889 evaluations
  (10.9 s, one thread). Evaluation rate ~23k/s per thread on this box (Xeon 2.1 GHz, AVX-512, 4 cores, 15 GB).
- Next order is any Haar graph with |G| ≥ 47,881. A result is a record iff 2|G| > 95,760.

## Why these groups

Orbit search (research/structured/STRUCTURE.md §2–3, §7): with α of order 3 (conjugation × z ↦ rz), the reachable
μ depends on μ_eff = μ/3 + |Fix(α)|·e^(−λ/3), λ = W/N, W(7,8) = 335,923. The record has μ = 43.0, μ_eff ≈ 16.06.
Groups in the window (N 47,881 … 49,000) checked with the one-step header of haar_sym (`MAXSTEPS=2`):

| group | N | 2N | μ | |Fix| | μ_eff | note |
|---|---|---|---|---|---|---|
| psl 11 × Z73 | 48,180 | 96,360 | 45.17 | 5 | 15.65 | prior run (seed 1, 3.9e6 evals) best cost 3 |
| pgl 9 × Z67 | 48,240 | 96,480 | 45.62 | 8 | 16.09 | new |
| psl 9 × Z134, sl 9 × Z67 | 48,240 | 96,480 | 45.62 | 17 | 16.98 | not run yet |
| prod psl 3 × psl 3 × Z333 | 47,952 | 95,904 | 43.49 | 26 | 17.1 | not run yet |
| psl 23 × Z8, psl 13 × Z44, psl 7 × Z288, sl 8 × Z96, sl 7 × Z144 | 48,048–48,576 | | 44–47 | 95–863 | ≥ 19 | too many fixed points, screened out |

Groups whose odd prime factors of n are ≡ 2 (mod 3) cannot carry an order-3 action on Z_n (e.g. Z11, Z5, Z17), so
they are excluded from the window (except the trivially acted 2-part, as in the record's Z14).

Earlier (7,8) rungs above the record (structured runs/): sl 11 × Z37 (48,840, μ 50.3) best 1 at 5.9e6 evals;
psl 19 × Z37 (126,540) irrelevant; sl 37 × Z1 (μ 66) best 10. Nothing in (47,880, 48,840] has been solved yet.

## Campaign log

### Phase A (2026-10-25, 08:03 UTC, one hour, four single-thread queues)

Jobs in `research/squads/cells/raise-d7D8/jobs/A*.jobs`, logs and any solution in `research/squads/cells/raise-d7D8/runs/`.

| queue | group | seed | variant | budget |
|---|---|---|---|---|
| A1 | psl 11 × Z73 | 11 | default | 3600 s |
| A2 | psl 11 × Z73 | 12 | ORBW=3 | 3600 s |
| A3 | pgl 9 × Z67 | 11 | default | 3600 s |
| A4 | psl 11 × Z73 | 13 | RESTART=1 | 3600 s |

Results (all four ran the full hour, about 1.2–1.4 × 10⁸ evaluations each, ~38k/s per thread):

| queue | group | variant | best cost | evals |
|---|---|---|---|---|
| A1 | psl 11 × Z73 | default | 3 | 1.38 × 10⁸ |
| A2 | psl 11 × Z73 | ORBW=3 | 3 | 1.37 × 10⁸ |
| A3 | pgl 9 × Z67 | default | 4 | 1.23 × 10⁸ |
| A4 | psl 11 × Z73 | RESTART=1 | 3 | 1.38 × 10⁸ |

Not solved. psl 11 × Z73 sits at cost 3 on every variant, a sign of a structural obstacle at this μ, not just
too little time (cost 3 ≈ one uncovered orbit or three uncovered fixed points). No solution to verify.

### Phase B (2026-10-25, 09:15 UTC, one hour, four single-thread queues)

Jobs in `research/squads/cells/raise-d7D8/jobs/B*.jobs`. prod psl 3 × psl 3 × Z333 (N = 47,952, so 2N = 95,904
> 95,760: a record if solved) has the lowest μ in the window (43.5) but μ_eff 17.1 and is solvable-heavy (A4 × A4),
so it is a real test.

| queue | group | seed | budget |
|---|---|---|---|
| B1 | prod psl 3 × psl 3 × Z333 | 11 | 3600 s |
| B2 | prod psl 3 × psl 3 × Z333 | 12 | 3600 s |
| B3 | psl 9 × Z134 | 11 | 3600 s |
| B4 | sl 9 × Z67 | 11 | 3600 s |

Results (one hour each, not solved):

| queue | group | seed | best cost | evals |
|---|---|---|---|---|
| B1, B2 | prod psl 3 × psl 3 × Z333 | 11, 12 | 31,968 (both) | 2.1 × 10⁷ |
| B3 | psl 9 × Z134 | 11 | 11 | 1.27 × 10⁸ |
| B4 | sl 9 × Z67 | 11 | 7 | 1.26 × 10⁸ |

The prod group is degenerate (cost ~3 × 10⁴ is the random level): A4 × A4 has almost no mixing, so it is ruled out.
psl 9 and sl 9 are well behind psl 11 × Z73.

### Phase C (2026-10-25, 10:16 UTC, 90 minutes, four seeds on psl 11 × Z73)

Jobs in `research/squads/cells/raise-d7D8/jobs/C*.jobs` (seeds 21–24, default variant, 5400 s each). These are the
only candidates left in the window with μ_eff near the record's (15.65 against 16.06).

Results: (pending)

## How to resume

- Binaries are not in git. Build from research/structured/haar_sym.c:
  `gcc -O3 -march=native -fopenmp -o haar_sym haar_sym.c -lm` (and `haar_fast.c`); `tools/haarcheck_psl.c` for
  PSL solutions above 20M vertices.
- Queue: `research/structured/tools/orbq.sh JOBFILE OUTDIR BIN` (sequential, one line per job, skips finished
  jobs, runs build_haar2.py on any solution). Run four queues in parallel, each with `THREADS=1`.
- A solution is saved as research/frontier/sols/d7D8_<group>_orb3_s<seed>.txt only after build_haar2.py says VALID.
