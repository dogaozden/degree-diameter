# Notes on bipartite (k,3,−2)-graphs (working file; the clean statements are in ../SUMMARY.md)

Notation as in SUMMARY.md §1: Γ is the oriented graph on the m = C(k,2) quads, g = k−2 = out-degree = in-degree,
M = 2I + A with MMᵀ = MᵀM = kI + 2J, W the signed A with WWᵀ = gI.

## Facts used or observed

1. Adjacent vertices have no common out- and no common in-neighbour; non-adjacent ones have exactly two of each
   (off-diagonal entries of MMᵀ, MᵀM).
2. Γ has no transitive triangle (a→b, a→c, b→c would give b, c adjacent with the common in-neighbour a). Every
   triangle is a directed 3-cycle.
3. (Lemma Q2) At any vertex u with out-set O, in-set I, rest R: O and I independent, no arcs I→O, R ≅ C(O,2) via
   common out-neighbours with u and R ≅ C(I,2) via common in-neighbours with u.
4. (2-factor lemma) For z ∈ I let S_z = {y ∈ R : y → z}, read as a set of pairs of O. Then S_z is a 2-regular
   simple graph whose vertex set is exactly O \ N⁻(z). (x → z: adjacent, so x and z have no common in-neighbour, so no
   pair in S_z contains x; x ↛ z: non-adjacent, exactly two common in-neighbours, u is not one of them.) So
   |N⁻(z) ∩ O| ∉ {7, 8} when g = 9. Dually for x ∈ O, the out-neighbours of x in R, read through φ as pairs of I,
   form a 2-regular graph on I \ N⁺(x).
5. Eigenvalues of A other than g lie on the circle |λ + 2|² = k (from MMᵀ = kI + 2J and normality). For k = 11 the
   underlying undirected graph cannot be strongly regular, and A² cannot be of the form τAᵀ + ν(J − I − A − Aᵀ).
6. Trace identity for k = 11: Σ over ordered pairs of (A²)²_cd = 12375, Σ (A²)_cd = 4455; (A²)_cd = 0 on arcs c→d.
7. Signing = linear system over GF(2): one equation s(c,e1)+s(d,e1)+s(c,e2)+s(d,e2) = 1 per "square"
   (c, d non-adjacent, {e1,e2} = their common out-neighbours). Each arc lies in exactly g−1 squares; there are
   C(m,2) − mg squares (one per non-adjacent pair; 990 for k = 11). No signing ⇔ some set of squares of odd size uses every arc
   an even number of times.

## k = 9 (the case where A exists but no signing does)

- A found by kissat in about 1.5 s (`analyze_quot.py 9`). Underlying undirected graph: strongly regular (36,14,4,6).
  Spectrum of A: 7, 1 (×21), −2 ± 3i (×7 each). A² = 4Aᵀ + (J − I − A − Aᵀ): a 3-class non-symmetric association
  scheme; every vertex lies on 28 directed triangles.
- Relative to vertex 0: the non-arcs from O to I form the incidence matrix of the Fano plane (each z ∈ I misses
  exactly a Fano line of O), and S_z is the triangle on that line.
- No signing: `signs_gf2.py A_k9.npy` finds a certificate of 13 squares on 26 arcs (every arc used twice). The
  13 squares form a quadrangulated sphere (15 vertices, 26 edges, 13 faces, Euler characteristic 2); adding their
  equations gives 0 = 1.
- CEGAR (`cegar.py 9`): two cuts (15 and 9 squares) and the A-only instance becomes UNSAT, 2 s in total.

## More facts (k = 11 unless said)

8. A is normal, its real eigenvalues are 9 and possibly −2 ± √11 (the only real points of |λ+2|² = 11), and complex
   eigenvalues come in conjugate pairs with conjugate eigenvectors. So the undirected graph G = A + Aᵀ has
   characteristic polynomial (x − 18)(x² + 8x − 28)^r · h(x)² with h ∈ Z[x] (every eigenvalue other than 18 and
   −4 ± 2√11 has even multiplicity).
9. Local 2-factor lemma at every vertex, in all four directions. For y ∈ R(u), its in-neighbours inside R(u), read
   as pairs of O(u), form a 2-regular graph on O(u) \ (P_y ∪ {x : x → y}). So the number c_y of in-neighbours of y
   in O(u) is in {0,1,2,3,4,7}; likewise a_y = |O(y) ∩ I(u)| ∈ {0,1,2,3,4,7}, and |N⁻(z) ∩ O| ∉ {7,8}.
10. Counting at a vertex u (t = number of arcs O→I = directed triangles through u):
    Σ_x C(α_x,2) + Σ_y C(a_y,2) = 72 and Σ_z C(β_z,2) + Σ_y C(c_y,2) = 72, with Σα = Σβ = t and
    Σa = Σc = 81 − t. Convexity then gives t ≤ 39.
11. Sub-cases run with kissat (`subcase.py`): B 4-regular at vertex 0 (t = 36) is UNSAT (195 s). "B has 36 arcs" and
    "rows of B have 4 ones" were not finished in 30 and 25 CPU-minutes, so fixing the column sums is what makes a
    sub-case easy. B 3-regular (t = 27): running.
12. The hard part is a small number of triangles. Degree cubes with t = 0 and t = 1 time out at 15 min, but with the
    extra (valid) choice "vertex 0 lies on the most directed triangles", so every vertex has at most t, they are
    UNSAT in 53 s (t = 0: no directed triangle anywhere) and 106 s (t = 1). `tmax.py` splits the whole instance into
    "every vertex on ≤ T−1 triangles" and "vertex 0 on ≥ T triangles".
