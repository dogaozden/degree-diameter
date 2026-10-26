# Cell (Δ, D) = (5, 10): raise job, round 2 (raise2-5-10)

Haar worker, branch `claude/raise-d5d10-haar-round2-tet4ac`, 2026-10-25 (Haiku 5.5, cloud).

## Starting point (verified this session)

- Round 1 (branch `claude/raise-d5d10-haar-otvuvl`, file `research/frontier/sols/d5D10_n95760_haar_pgl19x7_orb3f2.sol`):
  PGL(2,19) × Z7, N = 47,880, orbit k = 3, f = 2, **95,760 vertices**.
- Round-2 brief says the record is 95,472. Round 1 says it raised to 95,760 (its commit `0d5e7d0`). I re-verified the
  95,760 file with `research/frontier/build_haar2.py`: VALID, n = 95,760, 239,400 edges, 5-regular, ecc 10 from both
  sides, sha256 `89813309…593b5a` (matches round 1). **So the bar to beat is N > 47,880 (95,760 vertices).**
- The control run reproduces it: `haar_sym` with `ORBIT="3 1 2"`, pgl 19 × Z7, seed 1: solved at 289 evaluations,
  full diameter check OK.

## Tried in round 2 (so far)

Orbit recipe (k = 3, f = 2) on the valid candidates above 47,880 that round 1 had not run at (5,10), 240 s each,
one thread:

| group | N | μ | fixed | best (240 s) | evals |
|---|---|---|---|---|---|
| psl 11 × Z73, seed 1 | 48,180 | 34.1 | 5 | 410 | 7.7M |
| psl 8 × Z97, seed 1 | 48,888 | 38.4 | 8 | 2025 | 4.9M |
| psl 8 × Z97, seed 2 | 48,888 | 38.4 | 8 | 2025 | 4.9M |

Reading: a large cyclic factor (73 or 97) with a small Q is structurally bad for orbits, as round 1 found for
Z ≥ 73. Dead end.

## Orbit order-5 candidates (k = 5, f = 0: S = one free α-orbit of size 5)

For k = 5 the z-scaling needs primes p | n with p ≡ 1 (mod 5). Enumerating every Q × Z_n with Q from PSL/SL/PGL(2,q),
q ≤ 100, n ≤ 100, |Q·n| in (47,880, 52,000]: the only one with 5 | |Q| is **SL(2,9) / PGL(2,9) × Z71** (N = 51,120,
μ ≈ 54.8, μ/5 ≈ 11, ~10 fixed points). `enum.py` is in the scratchpad (not committed).


### Tool bug found on the way (fixed, committed `6d381cc`)

`haar_sym` hangs on any k = 5, f = 0 run: with one orbit and no fixed generators, S is the whole orbit, the
`AVOIDMASK` covers every index, and `walk()` loops forever in the targeted moves (`do j = rnd() % d; while (…)`). gdb
shows the hot path in `walk` called from `targeted`. The fix bounds the retry (64 tries); the targeting only picks
candidate elements and the cost evaluation stays exact. Round 1 did not reach this path (its k = 5 was "theory only").

### k = 5 on SL(2,9) × Z71 and PGL(2,9) × Z71 (N = 51,120, μ = 54.9, μ/5 = 11.0, |Fix| = 9)

- Start cost, seed 1: 528 (sl), 25,565 (pgl). Seed 2 starts: 42,600 (sl), 25,580 (pgl). The start cost depends strongly on
  the seed, unlike the orbit runs on the record group.
- Patched runs: sl seed 1 (150 s), sl seeds 2 and 3 and pgl seed 1 (stopped at 180 s, ~0.8M evaluations each).
  **SL plateau at exactly 134 for seeds 2 and 3 from 30 s on, with no change to 180 s.** PGL stuck at 25,560.
  Identical plateaus across seeds point at a structural floor, not search noise. Verdict: no k = 5 solution on this
  group in this budget. The only k = 5 group above 47,880 with these constraints is dead.

## Random-S (no symmetry) on the closest non-orbit candidates, 1 h per run (started 14:57 UTC)

Round 1's closest non-orbit point was sl 29 × Z2 (N = 48,720, μ 37.3): cost 2 after 30 min. Round 2 runs:
`haar_gen3 5 10 3600 SEED 8 … sl 29 2` for seeds 11, 12, 13, and `psl 11 73` (N = 48,180) for seed 21. Logs and
solution files in the scratchpad until results come in.

### Random-S results, 1 h each (ended 15:57 UTC), no solution

| group | N | μ | seed | best | evals |
|---|---|---|---|---|---|
| sl 29 × Z2 | 48,720 | 37.3 | 11 | 5 | 16.2M |
| sl 29 × Z2 | 48,720 | 37.3 | 12 | 4 | 17.7M |
| sl 29 × Z2 | 48,720 | 37.3 | 13 | **2** | 17.9M |
| psl 11 × Z73 | 48,180 | 34.1 | 21 | 9 | 4.1M |

Seed 13 reached cost 2 (same as round 1's best) and then stalled. No solution file was written.

## Stop assessment (round 2, 15:57 UTC)

Ruled out, with evidence:

1. **Orbit k = 3, f = 2 over Q × Z_n above 47,880.** The orbit recipe needs n with every prime factor ≡ 1 (mod 3). Enumerating
   all Q = PSL/SL/PGL(2,q), q ≤ 100, with n ≤ 100 gives only psl 11 × Z73, psl 8 × Z97, pgl/sl 9 × Z67, pgl/sl 11 × Z37,
   pgl/sl 37 (n = 1) and psl 47 (n = 1). Large cyclic factors (psl 11 × Z73 at cost 410, psl 8 × Z97 at cost 2025 after
   ~7M evaluations each) fail, and round 1 found the same for pgl 9 × Z67 and pgl/sl 11 × Z37 (floor 28). psl 47 has μ ≈ 62, far
   above the orbit wall, and so does sl 37 at μ ≈ 51.
2. **Orbit k = 5, f = 0.** The only group above 47,880 with a valid order-5 action is SL(2,9) × Z71 (N = 51,120). It plateaus
   at cost 134, identical across seeds, and PGL(2,9) × Z71 sits at 25,560. Both are structural floors for these runs.
3. **Random S (no symmetry)** at μ 34–37: best cost 2 in 1 h per run, from 17M evaluations. Round 1 saw the same wall.
4. **Route-chart lifts** (BEAT_16_5_SQUAD.md) need degree 4q; degree 5 is prime, so they do not apply.
5. **Non-Haar k-orbit voltage lifts** give the same μ at the same total order (λ depends only on total vertices), so they
   are no new lever on the random model. Not run.

Verdict: with the tools in this repo the cell does not move above 95,760 (N = 47,880). The best open lead is sl 29 × Z2
(N = 48,720, cost 2), which would give 97,440 vertices if a longer or better-tuned search reached cost 0. I'm stopping
here, since round 1 and this round both stall at cost 2 at μ ≈ 37.

## Status

- Verified the round-1 record 95,760 (pgl 19 × Z7, orbit k = 3, f = 2) with `build_haar2.py`. The round-2 brief says 95,472;
  the file says 95,760. Our bar is N > 47,880.
- No new record this round.
- Bug fixed in `research/structured/haar_sym.c` (commit `6d381cc`), so k = 5, f = 0 runs no longer hang.

# Round 3 (raise3-5-10), branch `claude/raise-d5d10-haar-round3-gz667b`

Bar: **N > 47,880** (vertices > 95,760). The brief's 95,472 is stale: round 1's file
`research/frontier/sols/d5D10_n95760_haar_pgl19x7_orb3f2.sol` is VALID under `build_haar2.py` (n = 95,760, ecc 10).
That file is on branch `claude/raise-d5d10-haar-otvuvl`; I did not copy it into this branch.

## Closed in this round (checks run here)

- **Orbit k = 3, f = 2 on the new small-n groups above 47,880** (60 s, 1 thread, K = 8). Costs after 60 s:
  psl 9×Z139 10,731; pgl 7×Z151 12,534; psl 7×Z301 29,181; psl 7×Z307 30,189; pgl 5×Z403 32,430;
  pgl 5×Z409 33,150; pgl 5×Z421 34,590; pgl 5×Z427 35,310; pgl 5×Z433 36,030; pgl 8×Z103 3,036; sl 9×Z67 205;
  pgl 3×Z1999 44,328. The cyclic factors (n ≥ 67) and small Q give large floors. Dead.
- **Orbit k = 2** (control pgl 19×Z7, which k = 3 solves in 289 evals): `ORBIT="2 2 1"` best 16 after 60 s;
  `ORBIT="2 1 3"` best 350. Weaker than random S here. Not pursued.

## Plan in progress

Metacyclic random-S sweep over N = 47,881–48,400 (18,781 candidates from `research/frontier/sizelaw/small_cands.py`),
screened with `RANDSAMPLE=1000` (score (p10 + median)/μ(N), μ from SIZE_LAW W = 349,525), then the top ones annealed
in order of N. Candidate screen and run logs are in the session scratchpad; this file gets the summary.

## NEW RECORD (round 3): (5,10) 95,964 vertices

- Haar graph of **Z727 ⋊₃₄ Z66** (metacyclic, N = 47,982, μ ≈ 32.9), d = 5, D = 10.
  Solution file `research/frontier/sols/d5D10_n95964_haar_meta727_66_34.sol` (header `5 10 meta 727 66 34 n 1 N 47982`).
- Found by `haar_gen3` annealing (seed 1, K = 8, 114.5 s, 1.48M evals) in the top-40 queue of the round-3 screen.
- Verification: `build_haar2.py` VALID (n = 95,964, 239,910 edges, 5-regular, bipartite, ecc 10 from both sides,
  edge-list sha256 `66486a07…d`); all-pairs BFS `research/lifts/coordinator_check/apsp.c` (no symmetry assumed):
  `n=95964 edges=239910 degree 5 5 bipartite=yes diameter=10`, VALID.
- New bar for further rounds: N > 47,982.

## Round 3 screen and first anneal queue (summary)

- Screen: all 13,099 metacyclic candidates with k ≥ 10 in N = 47,881–48,400 (k < 10 is ~10× slower per screen and
  none of the known records use it), `RANDSAMPLE=1000`, score (p10 + median)/μ(N). Ranking: meta 1143×42 (r 47) first.
- Queue 1: top 40 by score, 300 s each, seed 1, K = 8. 24 at 300 s; results below are the best costs at N > 47,880.
  One solve: 727×66 (r 34), N = 47,982, the new record. Cost 1 at N > 47,982: 1847×26 (r 123, N 48,022),
  982×49 (r 3, N 48,118). Cost 2: 1143×42 (r 47 and r 38, N 48,006), 2667×18 (r 164, N 48,006), 3694×13, 2189×22,
  2009×24 (r 68), 3719×13, 491×98.
- Queue 2 (running): 1200 s, seed 2, the cost ≤ 2 candidates above 47,982.
