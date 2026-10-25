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
- First patched 150 s run (sl, seed 1): cost 134 after 60 s, flat. Batch of 15 min (seeds 2, 3 sl; seed 1 pgl): in progress.
