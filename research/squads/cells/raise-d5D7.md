# raise-5-7: beat 3,120 vertices at the bipartite (Δ,D) = (5,7) cell

Job by a Haiku worker (claude-haiku-5-5), branch claude/raise-d5d7-haar-e7mw1h. Record to beat: 3,120 vertices
(N = 1,560 = |PGL(2,5) × Z13|, Haar graph, research/lifts/sols/d5D7_n3120_haar_pgl5xcyc13.txt). Table value 3,110.
Moore bound 10,922. Any Haar graph with N ≥ 1,561 (2N ≥ 3,122) is a new record.

## Status
- [x] Built haar_sym / haar_fast / haar_gen3 (research/structured, research/frontier; binaries not committed).
- [x] Baseline: haar_fast on pgl 5 × Z13 with plain annealing, 120 s, K=8: best cost 9 (not solved).

## Notes
(see the log below; newest last)

### 1. Orbit search is the lever (the plain annealer is near its wall)
- Plain annealing (haar_fast, pgl 5 × Z13 = 1,560, 120 s, K=8): best cost 9. Not solved.
- Orbit search (research/structured/haar_sym, ORBIT="k m f"; d = f + k·m = 5), same group, seed 1:
  - `3 1 2` (one α-orbit of size 3 plus two α-fixed generators incl. e): **cost 0 after 25 evaluations.**
    Rebuilt with research/frontier/build_haar2.py: VALID, 3,120 vertices, ecc 7 from both sides, degree 5.
  - `2 2 1`: cost 92 after 120 s. `4 1 1`: cost 170. `5 1 0`: stuck at its start cost 3,000.
  - So k = 3 is the shape to use for Δ = 5. Involutions and order-4 orbits create word collisions.
- Scratch runs and binaries live in the session scratchpad (not in git). Sweep config: `ORBIT="3 1 2"`, K=8, 300 s,
  one thread per run, four runs in parallel.
