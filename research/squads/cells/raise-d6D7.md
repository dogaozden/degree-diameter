# Cell (Δ, D) = (6, 7): raise job "raise-6-7"

Branch `claude/raise-d6d7-record-0em0u0`. Table value 8,310 (DS14v2). Bipartite Moore bound 39,062.
Our record before this job: **8,880** = Haar graph of SL(2,5) × Z37 (N = 4,440), k = 3, m = 2, f = 0
(two free α-orbits, α = conjugation by an order-3 element × z ↦ 10z). Found by the structured-search Opus session
(research/structured/STRUCTURE.md §4, §8). Logged solve: seed 2, 505 evaluations, at μ = 54.6 (μ/3 = 18.2,
|Fix(α)| = 5). That is far above the size-law wall (μ* ≈ 27 at this N), so this cell is easier than the Poisson model
says. Every step up in N is a new record.

## Method

`research/structured/haar_sym.c`, `ORBIT="3 2 0"` (f = 0), THREADS=1, K = 8, `tools/orbq.sh` job queue, four streams.
Binaries built into the session scratchpad (`gcc -O3 -march=native -fopenmp haar_sym.c -lm`).
Every solution checked with `research/frontier/build_haar2.py` (under 20M vertices). Record reproduced first:
seed 2 gives the same 505 evaluations as the logged run, and build_haar2.py says VALID for the 8,880 file.

Targets: N ≥ 4,441 (vertices 2N ≥ 8,882). Candidate groups come from
`tools/orb_screen.py 6 7 4441 6000 "3 2 0" --list`. Prefer SL (odd D: PSL and PGL carry involutions, which
collapse words, STRUCTURE §2.6). Every prime of n must be ≡ 1 (mod 3).

## Rung 1 triage (300 s per run, seed 1, K = 8, single thread)

Logs: `research/structured/runs/raise_d6D7/`. Cost = uncovered elements (0 = solved).

| group | N | μ | best cost | evals | result |
|---|---|---|---|---|---|
| psl 11 × Z7 | 4,620 | 67.4 | 14 | 2.6e7 | not solved (PSL: involutions) |
| psl 9 × Z13 | 4,680 | 72.1 | 25 | 2.4e7 | not solved |
| psl 5 × Z79 | 4,740 | 77.0 | 54 | 7.5e7 | not solved |
| sl 9 × Z7 | 5,040 | 104.6 | 48 | 2.3e7 | not solved |
| psl 7 × Z31 | 5,208 | 122.5 | 24 | 6.2e7 | not solved |
| sl 5 × Z43 | 5,160 | 117.2 | 72 | 6.5e7 | not solved |
| sl 5 × Z49 | 5,880 | 212.2 | 224 | 6.2e7 | not solved |
| prod psl 3 psl 3 × Z31 | 4,464 | 56.2 | 5,952 | 5.1e6 | not solved (poor mixing) |

## Rung 2 (300 s, seed 1)

| group | N | μ | best cost | result |
|---|---|---|---|---|
| psl 3 × Z373 | 4,476 | 57.0 | 3,388 | big cyclic factor, poor mixing |
| psl 3 × Z379 | 4,548 | 62.1 | 3,532 | same |
| sl 3 × Z193 | 4,632 | 68.3 | 790 | same |

Control on the record group (`sl 5 × Z37`, N = 4,440, μ = 54.6): seeds 1 and 3 solve in 2,705 and 2,801
evaluations (seed 2: 505). So the 8,880 solve is systematic, not a lucky seed, and it is an upper edge of what the
method reaches here so far: N = 4,440 is solved in seconds; every order above it has failed at 300 s.

Observations: groups whose cyclic factor is large against Q (A4 × Z373, SL(2,3) × Z193, A5 × Z79) mix badly.
PSL groups (involutions) sit at a higher floor than SL groups of similar order. Only SL-type groups with a
large Q relative to n are candidates above 4,440.

## Longer runs and the alternate scaling r

| group | N | μ | runs (seconds, evals) | best cost, every run |
|---|---|---|---|---|
| sl 9 × Z7 | 5,040 | 104.6 | 300 s (2.3e7); 1800 s ×2 (1.3e8 each); 900 s with r = 4 (6.7e7) | **48 in all five** |
| sl 5 × Z43 | 5,160 | 117.2 | 300 s (6.5e7); 1800 s (3.7e8); 900 s with r = 36 (1.9e8) | **72 in all three** |
| psl 11 × Z7 | 4,620 | 67.4 | 300 s (2.6e7); 1800 s (1.6e8) | **14 in both** |
| psl 9 × Z13 | 4,680 | 72.1 | 300 s (2.4e7); 1800 s (1.4e8) | **25 in both** |
| psl 7 × Z31 | 5,208 | 122.5 | 300 s (6.2e7); 1800 s (3.6e8) | **24 in both** |
| sl 17 × Z1 (SL(2,17)) | 4,896 | 90.6 | 600 s (4.0e7) | 28 |
| pgl 17 × Z1 | 4,896 | 90.6 | 600 s (2.1e7) | 118 |
| sl 5 × Z37, f = 3, m = 1 | 4,440 | 54.6 | 300 s (2.8e7) | 924 (f = 0 solves it in ~2.8k evals) |
| sl 5 × Z43, f = 3, m = 1 | 5,160 | 117.2 | 300 s (1.8e7) | 1,686 |

**Reading.** The best cost never moves once it reaches a value: the floors are identical across seeds, budgets
(300 s to 1800 s, up to 3.7e8 evaluations), and the choice of scaling r (two order-3 classes per group). That points to
a structural obstruction in orbit-symmetric S for these groups, not to a shortfall in compute. Two observations:

- The record group sits at zero because its orbit space has no such obstruction at N = 4,440, which is why its
  solve took ~2.8k evaluations on three seeds.
- PSL groups (involutions, the e^(−λ/2) penalty of STRUCTURE §2.6) have the lowest floors among the tried
  non-record groups (14, 24, 25), but none reached zero.

Small cyclic factors still mix poorly against a small Q (A4 × Z373 and A4 × Z379 stall near 3,400; SL(2,3) × Z193
near 790). Random-S annealing is not a substitute either: on the 4,220 metacyclic group (μ = 41, the previous
8,440 record) it reached best 4 in 90 s; the solve was an hour-scale job.

## Result

**Record unchanged: 8,880.** No solution found at any N ≥ 4,441 on the orbit route (k = 3, m = 2, f = 0) or on
f = 3, m = 1. Of the orders the screen lists (`tools/orb_screen.py 6 7 4441 6000 "3 2 0" --list`), these were run:
every SL/PSL/PGL candidate with a Q of order ≥ 60 and n ≤ 79 (sl 9×7, sl 5×43, sl 5×49, psl 11×7, psl 9×13,
psl 5×79, psl 7×31, sl 17×1, pgl 17×1), plus the small-Q cases psl 3×373, psl 3×379, sl 3×193 and prod psl 3 psl 3×31.
Not run: sl 3×199 (4,776), psl 3×397 (4,764), sl 3×211/217/223 (5,064 and up), pgl 5×43 and the other entries with
a small Q and a cyclic factor of order ≥ 100. Rung-2 data already rules those out (cost in the thousands).

I am stopping here, well before the 6-hour cap, because the floors are structural and reproducible. More compute on
these same groups would only repeat them. The decision the coordinator needs to make is whether a bigger model is
worth trying on the next step below.

## Next steps (for a bigger model or a new route)

1. **Diagnose the floor.** Dump the uncovered set at the best cost of `sl 9 × Z7` (cost 48) and `sl 5 × Z43` (cost 72).
   If the missed elements form a structured set (a coset, a subgroup, one z-class, central elements, a parity class
   of word lengths), the obstruction is the group, and the next N should avoid it. This is the one step with clear
   value before more search.
2. **Other route**: voltage lifts over a small base with structured voltages (research/lifts/, route-chart lifts,
   research/theorems/BEAT_16_5_SQUAD.md). Not attempted here.
3. **Odd-order groups** (no involutions, so no e^(−λ/2) penalty), e.g. Z_7² ⋊ Z_3 × Z_n. Not in the orbit tool's
   plain-group list; would need a family added to `haar_sym.c`.

## Notes for a resumed session

- Logs and build_haar2 verdicts: `research/structured/runs/raise_d6D7/` (every run listed above).
- Control solutions of the record (seeds 1 and 3) are in the same folder as `*.txt`; they are the 8,880 graph again,
  not new records.
- Command pattern: `ORBIT="3 2 0" THREADS=1 haar_sym 6 7 <secs> <seed> 8 <out> sl 5 43` (AR=<r> selects the scaling).
  `orbq.sh` skips any job whose log already has a RESULT line, so a new run needs a new seed.
- A winner must go to `research/frontier/sols/d6D7_<group>_orb3f0_s<seed>.txt` after build_haar2.py says VALID.
