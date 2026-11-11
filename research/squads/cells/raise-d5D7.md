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

### 4. Frobenius Z_p ⋊ Z_3 times abelian factors (exhaustive, fam2.py / sweep2.py)
- Groups Z_p ⋊ Z_3 (p ≡ 1 mod 3, inner order-3 conjugation, small centraliser) times every abelian A with
  3p·|A| ∈ [1561, 1700], at most 3 invariant factors. 82 (G, α, M) families with |Fix(α)| ≤ 20 done exhaustively; the
  6 families with |Fix| = 60–132 were skipped (too slow, and their Fix is far above the record's 6).
  Smallest |Fix| checked: 3 (Z_43⋊Z_3 × Z_13 and Z_79⋊Z_3 × Z_7, both order 1,677 / 1,659): no hit. Also no hit with
  |Fix| 6, 9, 12, 15, 18. Full log: raise-d5D7-tools/sweep2_out.txt.
- Bug found and fixed on the way: a wrong cube root of unity mod 67 and mod 79 gave a non-affine group (order 35,376);
  corrected (sweep2.py now uses r = 29 and 23).

## Status (end of session)
- Record **not raised**. Best N checked: none at N ≥ 1561 solvable under the methods above.
- Families exhausted (all k = 3 orbit-symmetric, exhaustive per (G, α)):
  - haar_sym grammar, N ∈ [1561, 1700], groups with an order-3 automorphism (~100 candidates, default α and AR).
  - A5 × abelian (Z2²×Z7, Z3×Z9, Z3³, Z28), S5 × abelian (Z14), PSL/SL/PGL(2,5)×Z14, Z_p ⋊ Z_3 × abelian (above).
  - Minima for the best of these: 30 (SL(2,5)×Z14), 42 (PSL(2,5)×Z28), 48 (PGL(2,5)×Z14), 52 (meta 133·12·8).
- Not tried (honest gaps): non-Haar bi-Cayley lifts with a larger base (the record came from a voltage lift session);
  groups outside the grammar and outside the abelian-factor extensions above (e.g. AΓL(1,8)×Z10, AΓL(1,9)×Z11,
  PGL(2,7)×Z5 under all α, S4 and A4 products); α with several different z-scalings on the same group beyond the
  automatic choice; the plain (non-symmetric) search at N ≥ 1561, which the annealer cannot reach (plateau at cost ~30).
- Judgement: the cell does not move with symmetric-orbit Haar graphs over the groups available here. A raise
  probably needs a new group source (a generic small-group library) or a non-Haar bi-Cayley/voltage search over a
  2-vertex base, which is beyond a Haar-worker's remit. Coordinator's call.

## Resume notes (for a fresh session)
- Binaries: `gcc -O3 -march=native -fopenmp -o haar_sym research/structured/haar_sym.c -lm`.
- Screen one (G, α) family exhaustively: `ORBIT="3 1 2" RANDORB=300000 ./haar_sym 5 7 1 1 8 /dev/null GROUP n`
  (min = family optimum). A hit is written with the same command and `out` path.
- Exact enumerator for perm-group bases × abelian factors: `python3 -I research/squads/cells/raise-d5D7-tools/sweep2.py`
  (edit the list at the bottom). `fam.py S5 13` reproduces the record (hit in 0.3 s). Verify any hit with
  `research/frontier/build_haar2.py`.
- Do not use the annealer in orbit mode for this cell: it stalls on its start plateau within 30 s.
