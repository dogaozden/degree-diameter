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

## Results

Record so far: 8,880 (unchanged).

## Notes for a resumed session

- Job files: `$SCRATCH/jobs/s*.jobs` (lost with the container; the lines are in the Results section once written).
- Logs and build_haar2 verdicts: `research/structured/runs/raise_d6D7/`.
- A winner must be copied to `research/frontier/sols/d6D7_<group>_orb3f0_s<seed>.txt`, verified with build_haar2.py
  (and haarcheck_sl / haarcheck_psl if > 20M vertices, not needed here).
