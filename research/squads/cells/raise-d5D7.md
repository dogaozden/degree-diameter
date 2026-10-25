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

### 2. Plain annealing and random sampling: what the numbers mean
- The annealer in orbit mode stops improving within ~30 s (it sits on its start plateau). So the k=3 orbit search is
  effectively *exhaustive enumeration* of the symmetric family for one (G, α): S = {e, t} ∪ O, t ∈ Fix(α), O an α-orbit
  of size 3; about |Fix|·N/3 sets in total (a few thousand). `RANDORB=300000` covers that whole family, so its `min` is the
  exact optimum of the family for that (G, α).
- Sweep, exact per family (α = inner conjugation × automatic z-scaling):
  - N = 1,568..1,700 groups in the haar_sym grammar (PSL/SL/PGL(2,q) × Z_n, AGL(1,q) × Z_n, Heisenberg, metacyclic
    Z_m ⋊ Z_k × 1, ~100 candidates): best minima: SL(2,5)×Z14 = 30, PSL(2,5)×Z28 = 42, PGL(2,5)×Z14 = 48,
    meta 133·12·8 = 52, AGL(1,16)×Z7 = 76. **No zero.** Several groups have no order-3 automorphism (skipped).
  - Control: the record group PGL(2,5)×Z13 (= S5 × Z13) has family minimum 0, as expected.
- Other orbit shapes are much worse on the record group (exact minima): 4 1 1 → 170, 2 2 1 → 92. k = 3 is the shape.
- Diagnostic: |Fix(α)| is what separates good from bad families. The record has |Fix| = 6 (incl. e); the 1,680 candidates
  have 12; metacyclic groups with a big centraliser have 200+.

### 3. Non-cyclic abelian factors (outside the haar_sym grammar)
- The grammar only allows cyclic Z_n factors. A5 × Z2² × Z7 (1,680; α fixed-point-free on Z2²), A5 × Z3×Z9 and
  A5 × Z3³ (1,620; α on the abelian part chosen with fewest fixed points) are new. A small Python enumerator
  (scratchpad fam.py / fam2.py; BFS on the Haar graph, both sides, D = 7) runs each family in ~2 s.
- Validation: it reproduces the record group (S5 × Z13: hit in 0.3 s). Non-cyclic results: no hit for A5×Z2²×Z7,
  A5×Z3×Z9, A5×Z3³ (all order-3 automorphisms with ≤ 3 fixed points), nor S5×Z14, A5×Z28.
