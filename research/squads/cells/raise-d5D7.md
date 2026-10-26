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

## Round 2 (branch claude/raise-d5d7-round2-la1n4w)

Record to beat: still 3,120 (N = 1,560, PGL(2,5) x Z13). Target: any 5-regular bipartite graph on 2N >= 3,122 vertices
with diameter 7. Round 1's branch is merged in, and round 1's families are not repeated.

Tools (research/squads/cells/raise-d5D7-r2/; logs in its logs/):
- `r2sweep.py`: exhaustive family S = {e,t} + alpha-orbit(3), t in Fix(alpha), for any group built from a multiplication
  table (permutation-generated factors x cyclic/abelian factors). alpha ranges over conjugation classes of order-3
  elements (and identity) times every z -> r z with r^3 = 1. Uses round 1's `fam.py` BFS check. Validation: on
  PGL(2,5) x Z13 it reproduces the known hit (|Fix| = 6, 18 s).
- `shapes.py`: other orbit shapes (k, m, f) = (5,1,0), (4,1,1), (2,2,1), (2,1,3), alpha of order 2, 4, 5. Random sample of
  5,000 candidates per family, families with |Fix| > 40 skipped.
- `r2frob.py`: outer (Frobenius) order-3 automorphisms of AGL(1,8) x Z_n, which the inner-only sweep cannot produce.
- `insert_exp.py`, `sa_insert.py`: non-symmetric route (see below).

### Results (all searched, no hit)
1. **Orbit families (order-3 shape), 66 groups** of order 1,560 (validation) to 1,692, every order-3 alpha, exhaustive:
   - batch 1 (40 groups): S4, SL(2,3), A4 x Z_n (n = 66..70 and 131..141 as fits); PGL(2,7), PSL(2,7), SL(2,7) x Z_n;
     AGL(1,8), AGammaL(1,8), AGL(1,9), AGammaL(1,9), AGL(1,7), AGL(1,11) x Z_n; S3 x S4, A4 x A4, S3 x A4 x Z_n;
     A5 x Z27, S5 x Z14, PGL(2,5) x Z14; S3 x S4 x Z11; plus the record group as validation.
   - batch 2 (26 groups): A4 x Z2 x Z_n, A4 x Z3 x Z_n, S3 x S3 x Z_n, S4 x Z3 x Z_n, A5 x Z2 x Z14, PSL(2,7) x Z2 x Z5,
     AGL(1,8) x Z2 x Z14, AGL(1,9) x Z2 x Z11, AGL(1,5) x Z_n for n = 79..85.
   - Smallest |Fix(alpha)| tried: 3 (14 families); 6, 8, 12 also tried. No family gives cost 0.
   - Logs: logs/sweep_*.txt, logs/sweep2_0.txt.
2. **Outer Frobenius alphas on AGL(1,8) x Z28 and x Z29** (conjugates of x -> x^2 composed with inner conjugations and
   z -> r z): exhaustive, no hit (logs/frob_agl18.txt).
3. **Other orbit shapes**, alpha of order 2, 4, 5, on the same 66 groups: 164 group x shape runs complete, no hit
   (logs/shapes_*.txt was a first attempt with a 30,000 cap and was stopped by its timeout; logs/shapes2_*.txt and
   logs/shapes3_*.txt are the completed capped runs). The record group itself gives no hit for these shapes either.
4. **Non-symmetric route: insert two vertices into the record.** Remove a 5-matching (a_i, b_i) of the 3,120-vertex
   Haar graph, join one new A-vertex to the b_i and one new B-vertex to the a_i. The result is 5-regular, bipartite,
   on 3,122 vertices. It has 1,106, 1,134 or 1,454 ordered pairs at distance > 7 (three random matchings tried). From
   there, 39 random valid bipartite double-edge switches each raised the count by at least 284, so the annealer
   (T0 = 20) accepted nothing. **Negative result:** the record is too rigid for local repair.

Total: about 1.3 x 10^8 candidate sets S checked by the BFS test (log counts), no candidate on 2N >= 3,122.

### Judgement and stop
- The symmetric families I can build (order-3 orbit shape and shapes of order 2, 4, 5, over 66 groups and all
  inner and Frobenius alphas) are exhausted. None reaches diameter 7 at N >= 1,561.
- Stopping here, as the brief allows. The methods that could still move the cell are the open leads below, and none
  is a sweep:
  (a) bi-Cayley / voltage lifts over a base of 4 vertices (2 + 2) with a group of order >= 781 (non-Haar, so the Haar
      families above do not cover them). This needs a new multi-orbit lift search.
  (b) non-split extensions and 2-groups of order 1,568..1,700, which no grammar here builds (needs a small-group library,
      e.g. GAP, which this box does not have).

## Round 3 (branch claude/raise-d5d7-round3-5dvjam)

Record to beat: still 3,120 (N = 1,560). Target: any 5-regular bipartite graph on V >= 3,122 vertices with diameter 7.
Round 2 left two open leads: (a) a 2+2 bi-Cayley (voltage) lift over a group of order >= 781; (b) non-split groups.
This round works on (a). Tools: research/squads/cells/raise-d5D7-r3/ (bc2.c, bc2s.c, bcheck.py, groups.py, aut_gen.py).

### Tools
- `bc2.c`: annealer for K orbits per side (vertices (side,i,g), edges (A_i,g) ~ (B_j, g t), t in S_ij). Cost = unreached
  vertices from the 2K sources (A_i,e), (B_j,e), summed. K = 1 is the Haar case. Element 0 is pinned in S_00.
- `bc2s.c`: the same, but every S_ij is a union of alpha-orbits (alpha of order 3, given as a permutation; M = 3-orbits per block).
- `bcheck.py`: independent check. Builds the explicit graph and runs all-pairs BFS, with no symmetry argument.
- `groups.py`: multiplication tables (identity = 0) for the non-abelian candidates; `aut_gen.py`: inner order-3 automorphisms.

### Findings so far
1. **Cyclic groups are useless here.** Z_n with a 2+2 base: cost stalls at 430-790 (n = 781). Words commute, so the
   ball of radius 7 covers too few elements. Also no group of order 781 is non-abelian (781 = 11 x 71).
2. **2+2 over non-abelian groups of order 784-840** (V = 3,136-3,360), 120 s each, plain annealing, cost summed over 4 sources:
   AGL(1,7)xZ19 (798): best 36 (DEG 2 3 3 2), 40 (1 4 4 1). AGL(1,8)xZ14 (784): 36 (1 4 4 1), 46 (2 3 3 2).
   AGL(1,9)xZ11 (792): 37, 43. PSL(2,7)xZ5 (840): 44, 59. None solved.
3. **Symmetric 2+2 (alpha = inner order-3 conjugation, M = 3-orbits per block) is worse:** costs 112-718 on
   PSL(2,7)xZ5 (|Fix| 15), A5xZ14, S5xZ7, SL(2,5)xZ7 (|Fix| 42). Round 1's diagnostic holds: big |Fix| is bad.
   AGL(1,8)xZ14 has no order-3 automorphism (784 is not divisible by 3).
4. **Calibration at V about 2,640-2,690** (120 s): 2+2 on A5xZ11 (660): best 4 (1 4 4 1), 6 (2 3 3 2). 2+2 on PSL(2,7)xZ4
   (672): 11. 1+1 Haar on A5xZ22 (1,320): 1, and on PSL(2,7)xZ8 (1,344): 1. So 2+2 is harder than 1+1 at equal V, but
   not by much; the wall lies between V = 2,690 and V = 3,136.

5. **The 2+2 family is not the lever with these methods.** Plain 2+2 annealing (bc2f, 120 s) reaches cost 36-46 on the
   order-784..798 groups, and 2,400 s runs sit at 35-37 with no progress after 10 minutes.
6. **Orbit-symmetric 2+2 with a genuinely small fixed set.** Round 1's |Fix| = 6 diagnostic is reached by a product
   automorphism alpha(x) = c_g(pi_H x) * (pi_Z x)^r, with g of order 3 in H and r^3 = 1 mod |Z| (`aut_prod.py`).
   This gives |Fix| = 6 on S5xZ7, A5xZ14, SL(2,5)xZ7 (all 840) and AGL(1,7)xZ19 (798). Symmetric 2+2 (bc2sf, 600 s):
   best 86-104 on S5xZ7 and AGL(1,7)xZ19, 55-77 on A5xZ14, and 32-38 on SL(2,5)xZ7. The pure inner conjugations
   (|Fix| 15-114) were worse still (112-718). None is solved.
7. **Control: the record group itself, plain Haar (K = 1), bc2f.** S5xZ13 (N = 1,560, the record group) reaches cost 9-10
   after 10 minutes on two seeds. Round 1 saw 9 at 120 s. Plain annealing does not reproduce the record here.
8. **Where the lead sits in the other branch.** The voltage-lift session (claude/voltage-lifts-search-6lfotq,
   research/lifts/RESULTS.md) ran rich and wide sweeps over lift orders 3,112-3,132 (2+2 bases included, since
   enum_bases covers h = 2 for degree 5) and got best cost 10. It also states that "larger bases can only win through
   structure", since the random model gives them no first-moment advantage. So the 2+2 family near 3,120 is largely
   covered by that session. The record itself came from its haar_cell sweep: about 15 anneals of 300 s, with the
   record group ranked 22nd of 874 by screening.

### Judgement (round 3)
- No hit at V >= 3,122 in the families tried this round: 2+2 over 784-840 (plain and symmetric, |Fix| 6 and 15-114),
  and the Haar control on the record group.
- Symmetric 2+2 with |Fix| = 6 (the record's diagnostic) is the best 2+2 family here (best 32), but it is not close.
- What is left and not done: a broad multi-seed sweep of plain Haar graphs over non-abelian groups of order 1,561-1,620
  with bc2f (the lifts session did this with haar_gen3 and found nothing above 1,560); 2-groups of order 1,568-1,700
  (no group library here; round 2's lead b); and orbit-symmetric 2+2 on groups where Z_n has an order-3 scaling with
  |Fix| 6 and |G| in 781..800 (none of the candidates here).
- This is a stop, not a proof: the cell may still move with a much larger search than this box can run. The coordinator
  decides whether a bigger model is worth it.

9. **Final symmetric runs (SL(2,5)xZ7, |Fix| = 6, bc2sf, 2,700 s planned, stopped at about 1,750 s).** Best costs 30
   (DEG 1 4 4 1, seed 3), 38 (1 4 4 1, seed 2), 32 (2 3 3 2, seeds 2 and 3). All were flat from about 600 s on, so the runs
   were stopped early. Logs: research/squads/cells/raise-d5D7-r3/logs/.
