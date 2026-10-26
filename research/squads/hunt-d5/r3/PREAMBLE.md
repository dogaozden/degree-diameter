# hunt-d5 squad, round 3: preamble (read ../r1/PREAMBLE.md for the problem, machine rules and output format)

Same rules: single thread (THREADS=1), every run `timeout <s> nice -n 10`, about 12 CPU-minutes, 35 minutes wall
clock, no git, write only in `research/squads/hunt-d5/r3/<card>/`, one JSON line to `research/squads/hunt-d5/r3/scoreboard.jsonl`.

## What rounds 1–2 found (all cost > 0)

The best Haar near misses in every cell are metacyclic groups (Z_p ⋊ Z_k, often times a small cyclic group):
- (9,5): (Z53 ⋊ Z13) × Z2 (order 1,378, = SmallGroup(1378,2)): **cost 4** (several seeds); Z197 ⋊ Z7 (1,379): 6.
- (7,5): (Z41 ⋊ Z5) × Z3 (615, = SmallGroup(615,1)): **cost 4** (2 of 41 seeds); 609/1, 610/2: 6. All
  orbit-symmetric S of 615/1 (automorphisms of order 2–5) are exactly ≥ 12, and its exact 3-swap neighbourhood is ≥ 4.
- (6,5) (new cell, published 684): Z71 ⋊ Z5 (355): **cost 2**; (Z7 ⋊ Z3) × Z17 (357): 4; Z13 ⋊ Z27 (351): 6. The
  director is running an exact certificate for Z71 ⋊ Z5 — skip that group.
- (5,5): the director is running an exhaustive search over every group of order 193–215 (done for many already).
- Dead: lifts of K_{Δ,Δ}, coset-union S, orbit-symmetric S at D = 5 (always worse), q = 2 route charts so far.

## The tool for this round: haar_fast (13× faster than haar5 on these groups)

`THREADS=1 ../../tools/haar_fast d 5 SECONDS SEED K OUT meta p k r n` — annealing over Haar graphs of
G = (Z_p ⋊_r Z_k) × Z_n ((a,j)(b,l) = (a + r^j b, j + l); r^k ≡ 1 mod p). Prints `RESULT ... best=<cost>`; at cost 0
it writes OUT. Env: COOL (seconds per halving of the temperature, default 20), REHEAT (seconds without gain before a
reheat, 150), K is the 5th argument (candidates per move, 16 is a good default). Verify any cost 0 with
`python3 ../../../../frontier/build_haar2.py OUT X.edges` (must print VALID) and then `../../tools/apsp X.edges d 5`.
Group lists: `meta_specs_d5.txt`, `_d6`, `_d7`, `_d9` in this folder (sorted by μ = N·e^(−W/N); prefer p ≥ 23).
Lesson from the earlier D = 5–10 runs: on near misses, many short seeds beat a few long runs.
