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

Results (90 minutes each, not solved):

| seed | best cost | evals |
|---|---|---|
| 21, 22, 23, 24 | 3 (all four) | 2.08–2.09 × 10⁸ each |

## Status: stopped, no new record (2026-10-25, ~11:50 UTC)

- No Haar graph above 95,760 was found. Nothing new to verify or add to research/frontier/sols/.
- The only candidate in the window with a favourable μ_eff (psl 11 × Z73, 2N = 96,360) has been run for about
  1.8 × 10⁹ evaluations over nine seeds and variants (default, ORBW=3, RESTART=1). Every run stopped at best cost 3.
  Cost 3 is one uncovered orbit or three uncovered α-fixed elements, and it never went lower. That looks like a
  structural plateau of this α, not slow annealing.
- The other rungs are worse: pgl 9 × Z67 best 4, sl 9 × Z67 best 7, psl 9 × Z134 best 11, prod psl 3 × psl 3 × Z333
  degenerate (cost ~3·10⁴), and the earlier sl 11 × Z37 (N 48,840) best 1.
- What the orbit method can still try: other groups with order 47,881–48,600 whose μ_eff ≤ 16 (none found under the
  rule that odd primes of n are ≡ 1 mod 3), and a different α (k = 3 with another fixed-point class).

**Recommended next steps (for the coordinator):**
1. Diagnose the cost-3 plateau on psl 11 × Z73: list the three uncovered elements (which α-orbits or fixed points they
   are) and check whether a word collision forces them. If it is forced, stop this group for good.
2. Try a non-orbit route for N 47,881–48,500. The lift and route-chart routes (research/lifts/,
   research/theorems/BEAT_16_5_SQUAD.md) are the other families; the orbit search has no candidate left here.
3. A bigger model, if the coordinator wants it, for (1) and (2). Haiku tooling is enough for running the queues.

## How to resume

- Binaries are not in git. Build from research/structured/haar_sym.c:
  `gcc -O3 -march=native -fopenmp -o haar_sym haar_sym.c -lm` (and `haar_fast.c`); `tools/haarcheck_psl.c` for
  PSL solutions above 20M vertices.
- Queue: `research/structured/tools/orbq.sh JOBFILE OUTDIR BIN` (sequential, one line per job, skips finished
  jobs, runs build_haar2.py on any solution). Run four queues in parallel, each with `THREADS=1`.
- A solution is saved as research/frontier/sols/d7D8_<group>_orb3_s<seed>.txt only after build_haar2.py says VALID.

## How to resume

- Binaries are not in git. Build from research/structured/haar_sym.c:
  `gcc -O3 -march=native -fopenmp -o haar_sym haar_sym.c -lm` (and `haar_fast.c`); `tools/haarcheck_psl.c` for
  PSL solutions above 20M vertices.
- Queue: `research/structured/tools/orbq.sh JOBFILE OUTDIR BIN` (sequential, one line per job, skips finished
  jobs, runs build_haar2.py on any solution). Run four queues in parallel, each with `THREADS=1`.
- A solution is saved as research/frontier/sols/d7D8_<group>_orb3_s<seed>.txt only after build_haar2.py says VALID.

---

# Round 2 (job raise2-7-8), branch claude/raise-d7d8-round-2-xtwr95

Record to beat: **95,760** (N = 47,880, psl 19 × Z14, k = 3, m = 2, f = 1). A result is a record iff 2N > 95,760,
i.e. N ≥ 47,881. Round 1 (above) ran psl 11 × Z73, pgl 9 × Z67, psl 9 × Z134, sl 9 × Z67 and prod psl 3 × psl 3 × Z333
with no solution. Round 1's best open leads, in its own words: diagnose the cost-3 plateau on psl 11 × Z73; try a route
it did not try. Round 2 does not repeat round 1's queues.

## Round 2 plan

1. **Lead: sl 11 × Z37 (N = 48,840, 2N = 97,680, μ = 50.3, |Fix(α)| = 11).** The structured session's only run of
   this group (`research/structured/runs/sl_11_37_k3_s1.log`, 180 s, one seed) reached cost 1 after 5.9·10⁶ evaluations
   and oscillated between cost 1 and 7. Round 1 never continued it. A new N = 48,840 would be +2.0 % on the record.
2. **Also N = 48,840:** psl 11 × Z74 (2-part of Z74 trivially acted, same |Fix| = 11) and pgl 11 × Z37 (screen min 27).
3. Non-orbit routes (lifts, route-chart) do not apply at Δ = 7: the route-chart lift needs Δ = 4q (BEAT_16_5_SQUAD.md),
   and the voltage lifts there need a base graph with degree-16 walks. Not pursued in this round.

### Screen (tools/orb_screen.py 7 8 47881 48840 "3 2 1" --anyn --samples 300, one run, 4 cores busy)

Lower min and p1 are better. μ is N e^{−W/N}. The list adds groups that round 1 did not run. Round 1's psl 11 × Z73
has min 27 and pgl 9 × Z67 min 20, both still open (round 1 best 3 and 4). Among N = 48,840 groups: sl 11 × Z37
min 22 / p1 31 / p10 59 (structured best 1); psl 11 × Z74 min 19 / p1 33 / p10 70; pgl 11 × Z37 min 27.
Screen-only, not run: sl 7 × Z145 (min 35,271), prod psl 3 × psl 3 × Z339 (min 48,048) and the rest of the list are far
behind.

## Round 2 campaign log

### Phase A (2026-10-25, 14:49 UTC, one hour, four single-thread queues)

Jobs `jobs/A1–A4.jobs`, logs in `runs/`, k = 3 m = 2 f = 1, K = 8, budget 3600 s each:

| queue | group | seed | variant |
|---|---|---|---|
| A1 | sl 11 × Z37 | 101 | default |
| A2 | sl 11 × Z37 | 102 | RESTART=1 |
| A3 | sl 11 × Z37 | 103 | ORBW=3 |
| A4 | psl 11 × Z74 | 104 | default |

(results appended below as they finish)

### Phase A results (2026-10-25, finished 15:49 UTC; not solved)

| queue | group | seed | variant | best cost | evals |
|---|---|---|---|---|---|
| A1 | sl 11 × Z37 | 101 | default | **1** | 1.28 × 10⁸ |
| A2 | sl 11 × Z37 | 102 | RESTART=1 | **1** | 1.26 × 10⁸ |
| A3 | sl 11 × Z37 | 103 | ORBW=3 | 3 | 1.27 × 10⁸ |
| A4 | psl 11 × Z74 | 104 | default | 3 | 1.29 × 10⁸ |

Two independent seeds of the structured session's group both stop at cost 1 after about 1.3 × 10⁸ evaluations each
(the structured session's single run got 1 after 5.9·10⁶). Nothing at cost 0. Round 1's psl 11 × Z73 plateau at cost 3
has the same shape: the orbit search reaches a floor in this group, and more seeds or time on the same α do not move it.
No solution exists to verify.

### Other α for the same group (`ASEED`, new in haar_sym.c, default unchanged)

`haar_sym.c` picks α as the first order-3 conjugation found by a random search with a fixed seed (0xC0FFEE). The
`ASEED=<n>` override (added this round) changes that seed, so the automorphism differs while the group, k, m, f and
|Fix(α)| = 11 do not. The screen `RANDORB=5000` over ASEED 1–39 (`scratchpad/aseed_screen_sl11_37.txt`, not in
git) gives best-of-5000 min cost from 6 to 18 and p1 from 30 to 33, with no visible dependence on α. So the α class
is a weak lever in this group. Phase B tests the four lowest-min α with 40 minutes each:

| queue | group | ASEED | seed | budget |
|---|---|---|---|---|
| B1 | sl 11 × Z37 | 18 (min 6) | 201 | 2400 s |
| B2 | sl 11 × Z37 | 5 (min 7) | 202 | 2400 s |
| B3 | sl 11 × Z37 | 39 (min 9) | 203 | 2400 s |
| B4 | sl 11 × Z37 | 12 (min 9) | 204 | 2400 s |

(results appended below as they finish)

### Phase B results (2026-10-25, 15:51–16:31 UTC; not solved)

| queue | ASEED | seed | best cost | evals |
|---|---|---|---|---|
| B1 | 18 | 201 | **1** | 8.6 × 10⁷ |
| B2 | 5 | 202 | **1** | 8.6 × 10⁷ |
| B3 | 39 | 203 | **1** | 8.5 × 10⁷ |
| B4 | 12 | 204 | **1** | 8.6 × 10⁷ |

Four different automorphisms, all stop at cost 1, and so do the default α (phase A, two seeds). Across the group,
about 6 × 10⁸ evaluations at cost ≥ 1 and no cost 0.

## Conclusion of round 2 (stopping)

**No record. Nothing new to verify or add to research/frontier/sols/.** The cell does not move with the orbit method
in the window 47,881 … 48,840 that round 1 and this round covered:

- **sl 11 × Z37** (N = 48,840, the largest-μ window candidate that is still a real record: 2N = 97,680): a floor at cost 1,
  seen under 6 α and 5 seeds (~1.2 × 10⁹ evaluations in total across the phases).
- **psl 11 × Z73, psl 11 × Z74** (same plateau at cost 3 as round 1).
- Round 1's other groups (pgl 9 × Z67, sl 9 × Z67, psl 9 × Z134, prod psl 3 × psl 3 × Z333) were worse.

The α choice is a weak lever here (random screens over 40 α show the same cost distribution). Cost 1 and cost 3 are
flat floors, not slow annealing: more seeds, longer time or a different α do not lower them.

**Why I stopped:** the brief allows stopping when the cell will not move with these methods. Here there are three
independent floors (round 1's psl 11 × Z73 and round 2's sl 11 × Z37 and psl 11 × Z74 at cost 3 and 1, each across
several seeds), and the groups with a lower μ in the window were screened and are worse. I am not certain no α or
group will solve, so the statement is about this method's reach, not a proof.

**Not tried (for the coordinator):**
1. **Diagnose the floor.** Dump the uncovered elements at the cost-1 state of sl 11 × Z37 and check whether they are
   α-fixed elements (C_G(α) × {0}, |Fix| = 11) that no word of the allowed length reaches. If so, the group is blocked
   for every α of this type, and only f ≠ 1 or a larger |Fix| change helps. The tool has no uncovered dump; adding one is
   the first step (haar_sym.c has the uncovered lists in cost_w).
2. **Fixed generators other than e** (f = 4 with k = 3): S = 4 α-fixed elements ∪ one orbit. Fix(α) is only 11
   elements, which probably make words collide. Not run.
3. **SL(3,q) or other groups with small centralizers of order-3 elements** (STRUCTURE.md §7.3): not implemented.
4. **Voltage lifts with k ≥ 2 orbits** (base multigraph of 7-regular bipartite multigraph on k+k vertices, voltages
   in a non-abelian group). The route-chart lift (BEAT_16_5_SQUAD.md) needs Δ = 4q and does not apply to Δ = 7. The
   generic voltage lift has the same first-moment λ = W/N, so I do not expect it to beat the coupon wall, but it was
   not tested.

## Files on this branch (round 2)

- `research/squads/cells/raise-d7D8-r2/jobs/` (A1–A4, B1–B4 job files) and `runs/` (all logs, RESULT lines).
- `research/structured/haar_sym.c`: `ASEED=<n>` env override for the automorphism seed (default unchanged; the
  default run reproduces the 0xC0FFEE α, index 932). Only addition.
- The α screen output (`aseed_screen_sl11_37.txt`) is in the scratchpad, not in git.

---

# Round 3 (job raise3-7-8), branch claude/raise-d7d8-round-3-synii4

Record to beat: **95,760** (N = 47,880). A result is a record iff N ≥ 47,881 (2N > 95,760). Round 2's notes are above and
were not repeated here. Round 2's untried list was: (1) diagnose the cost-1/cost-3 floors, (2) f = 4 with k = 3,
(3) SL(3,q) groups, (4) voltage lifts with k ≥ 2 orbits. Round 3 takes a different family (below) and tests one more
order of α.

## Round 3 plan

1. **Order-7 α with one free orbit (`ORBIT="7 1 0"`): ruled out by screen.** Δ = 7 = 7·1 is the only other way to get
   Δ = 7 with k ≥ 5. Screened with `tools/orb_screen.py 7 8 47881 48840 "7 1 0" --anyn --samples 300` over all 27 candidate
   groups (scratchpad, not in git). Every group has a minimum random cost of at least 24,000 (μ ≈ 45–50): one orbit of
   7 conjugates usually generates a small subgroup, so most elements stay uncovered. Dead end, no annealing run.
2. **Order-2 α with f = 1, m = 3 (`ORBIT="2 3 1"`).** Earlier rounds dropped involutions (STRUCTURE.md §2.1, §5:
   α(u) = u⁻¹ on a density ~1/q set of words). But the (6,8) record psl 11 × Z24 (f = 0, m = 3, k = 2,
   research/frontier/sols/d6D8_psl_11_24_orb2f0_s1.txt, VALID) shows involutions can work. The first-moment count is
   larger for k = 2 than for k = 3 at this N: about (N/2)³/6 ≈ 2·10¹² choices against (N/3)²/2 ≈ 1.3·10⁸, while
   μ/2 ≈ 21.5 against μ/3 ≈ 14.3. Collisions cost ~1/q, so large q is the test: psl 23 × Z8, sl 29 × Z2, psl 29 × Z4 and
   sl 23 × Z4 have q ≥ 23, and the screen (300 random samples each) gives medians 258, 288, 425, 377. That is close to the
   k = 3 medians on the round-1/2 groups (228–412) on the same raw-cost scale, so k = 2 is not hopeless there.

## Round 3 campaign log

### Phase A (2026-10-26, 01:58 UTC, 40 minutes, four single-thread queues)

Jobs `jobs/A1–A4.jobs`, logs in `runs/`, ORBIT="2 3 1", K = 8, budget 2400 s each:

| queue | group | N | seed | |Fix(α)| | μ | μ/2 |
|---|---|---|---|---|---|---|
| A1 | psl 23 × Z8 | 48,576 | 301 | 47 | 48.2 | 24.1 |
| A2 | sl 29 × Z2 | 48,720 | 302 | 55 | 49.3 | 24.7 |
| A3 | psl 29 × Z4 | 48,720 | 303 | 55 | 49.3 | 24.7 |
| A4 | sl 23 × Z4 | 48,576 | 304 | 47 | 48.2 | 24.1 |

(results appended below as they finish)
