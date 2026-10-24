# (Δ, D) = (13, 7): beating 1,062,936 by surgery on the three-copy hexagon graph

Job "cell-13-7" (Opus + Haiku squads), 2026-10-24, cloud session. Status: see §5 for the current best and its checks.

## 1. Where the table value comes from

The table value 1,062,936 is exactly 3 × 354,312, three copies of the incidence graph of the split Cayley hexagon
H(11) (a generalized hexagon of order (11,11), the (12,6) bipartite Moore graph). The same pattern explains the whole
large-Δ part of the D = 7 column: (7,7) = 3·GH(5), (9,7) = 3·GH(7), (10,7) = 3·GH(8), (11,7) = 3·GH(9),
(13,7) = 3·GH(11), (12,7) = 5·GH(9), (14,7) = 5·GH(11), (16,7) = 5·GH(13), (15,7) = 7·GH(11), i.e.
n_b(q+1+r, 7) ≥ (2r+1)·2(q+1)(q⁴+q²+1). For r = 1 the construction is:

- vertices (x, i), x a point or line of H, i ∈ Z3; the hexagon's incidences inside each copy;
- one extra matching (p, i) ~ (σ(p), i+1) for a bijection σ: points → lines.

**Any bijection σ works.** A point x of copy i reaches all of copy i+1 through its own matching edge (a line
reaches everything within 6, a point within 5, in H), and reaches a point t of copy i−1 through the line σ(t) of
copy i (point–line distance ≤ 5 in H). That is the whole proof (§3 lists the cases). So σ is a free parameter
of 177,156! bijections, and that freedom is what we use.

Haar / Cayley search cannot get here: at N ≈ 531,500 the Poisson mean of uncovered elements is μ ≈ 1,160 against a
first-moment ceiling ≈ Δ ln N ≈ 171 (research/structured/STRUCTURE.md §6 already lists "D = 7 with Δ ≥ 9" as above
the ceiling). Multi-copy alternatives (4 copies, twisted lifts of H(11) + matching over Z4 or Z2², GH(13) minus a
2-factor) all need either a duality of H(11), which does not exist (H(q) is self-dual only for q = 3^h), or
random-like coverage with redundancy 2–3, which fails by orders of magnitude (§6).

## 2. The surgery

Choose a set R of points and remove the three matching edges at (r, 0), (r, 1), (r, 2) for every r ∈ R. That frees
one slot at each (r, i) and at each (σ(r), i). Add, for every r ∈ R,

- a vertex v_r joined to (r, 0), (r, 1), (r, 2), and a vertex u_r joined to (σ(r), 0), (σ(r), 1), (σ(r), 2);
- edges v_r ~ u_s for s − r in a fixed set of residues (a circulant NS of degree ≤ q − 1 = 10), so that any two
  v's and any two u's are within distance 6 inside NS.

Max degree stays q + 2 = 13, the graph stays bipartite, and it has 6(q+1)(q⁴+q²+1) + 2|R| vertices.

**Theorem.** Let H be a generalized hexagon of order (q, q), q ≥ 3, σ a bijection from points to lines, and R a
set of points such that
(H1) the points of R are pairwise opposite (distance 6 in the incidence graph);
(H2) the lines of σ(R) are pairwise opposite;
(H3) σ is a *local duality* on R: σ(Γ₂(r)) = Γ₂(σ(r)) as sets, for every r ∈ R, where Γ₂(r) is the set of q(q+1)
     points collinear with r and Γ₂(ℓ) the set of q(q+1) lines meeting ℓ;
(H4) NS has v–v and u–u distances ≤ 6 and max degree ≤ q − 1.
Then the graph above has diameter ≤ 7.

*Covering lemma.* For a line ℓ, every point x is at distance ≤ 3 from some line of Γ₂(ℓ) (take the line of Γ₂(ℓ) on
a shortest path from ℓ to x; d(ℓ, x) ∈ {1, 3, 5}). Dually, for a point p every line is within distance 3 of a point
of Γ₂(p).

*Proof.* Pairs inside one copy: the hexagon is untouched (distance ≤ 6). For copies i and i+1 take a pair
{(a, i), (b, i+1)}.
- a a point, a ∉ R: (a,i) → (σ(a), i+1) → b, length 1 + d(σ(a), b) ≤ 7 (≤ 6 if b is a point).
- a a line, b a point: choose a line m ∋ b with m ∉ σ(R) (by H2 at most one line of σ(R) passes through b);
  (a,i) → (σ⁻¹(m), i) → (m, i+1) → (b, i+1), length ≤ 5 + 1 + 1 = 7.
- a a line, b a line, b ∉ σ(R): (a,i) → (σ⁻¹(b), i) → (b, i+1), length ≤ 6.
- a = r ∈ R, b a point: (r,i) → (p′, i) with p′ ∈ Γ₂(r) (not in R by H1) → (σ(p′), i+1) → b. By H3 the lines σ(p′)
  run over Γ₂(σ(r)), so by the covering lemma some σ(p′) is within distance 3 of b: length ≤ 2 + 1 + 3 = 6.
- a = r ∈ R, b a line: (r,i) → v_r → (r, i+1) → b, length ≤ 2 + 5 = 7.
- b = σ(r) ∈ σ(R), a a line: (σ(r), i+1) → (ℓ′, i+1), ℓ′ ∈ Γ₂(σ(r)) → (σ⁻¹(ℓ′), i) → a. By H3 the points σ⁻¹(ℓ′)
  run over Γ₂(r) (not in R, so their matching edges exist), and by the dual covering lemma one of them is within
  distance 3 of a: length ≤ 6.
New vertices: v_r reaches every vertex of copy i through (r, i) (≤ 1 + 6 = 7 to points, ≤ 1 + 5 = 6 to lines),
u_r likewise through (σ(r), i); v_r–u_s ≤ 2 + 5 = 7 through one copy; v–v and u–u by H4. Every pair is covered;
parity is automatic (bipartite). ∎

(The three cases "a ∉ R", "b ∉ σ(R)" are exactly the routes of the plain construction; the damaged pairs are only
those with an end at some (r, i) or (σ(r), i), and those are the repaired cases. Because R is pairwise opposite, the
sets Γ₂(r) are pairwise disjoint and so are the Γ₂(σ(r)), so H3 can be imposed independently for each r and σ is
arbitrary elsewhere.)

## 3. What R can be (the real problem)

In H(q) ⊂ Q(6,q), two points are at distance ≤ 4 iff they are orthogonal for the quadric's bilinear form
(checked on 20 random points against BFS; also |x^⊥ ∩ Q(6,q)| = 16,105 = 1 + 132 + 15,972). So **R is a partial
ovoid of the polar space Q(6,11)**: points pairwise non-orthogonal. For σ(R), the Hermitian spread (the 1332 = q³+1
lines of H(11) inside an elliptic hyperplane x4 = −x0) gives up to 1332 pairwise opposite lines, so the points are
the only bottleneck. Ovoids of Q(6,q) (q³+1 points) exist only for q = 3^h; for q = 11 the maximum is unknown.

| method | |R| | graph order |
|---|---|---|
| random greedy | ~100 | 1,063,140 |
| elliptic 3-space section Q⁻(3,11) (maximal, not extendable) | 122 | 1,063,180 |
| iterated local search (povoid_ils), penalty annealing, LNS (squad r1 c2, c5) | 133–136 | ≤ 1,063,208 |
| ILS seeded with pieces of 16 elliptic sections (r1 c6) | 282 | 1,063,500 |
| **e4 + k parallel affine lines** (r1 c3: k = 22; r1 c8: k = 29) | 1 + 11k = 320 | **1,063,576** |

*The fibration (squad round 1, card c3; card c8 independently).* The points opposite e4 = (0,0,0,0,1,0,0) are the
affine points x = (1, a, b, c, c² − ae − bf, e, f), and B(x, x′) = Q′(Δ) with Q′(a,b,c,e,f) = c² − ae − bf. Take
k whole affine lines t + F₁₁u with Q′(u) = 2 (a non-square). Inside a line all differences are λu (fine);
two lines are compatible iff the quadratic λ ↦ Q′(c + λu) has no root, c = t − s, which depends only on c modulo u
and is a quadratic-character condition on an elliptic 4-dimensional form. So the lines form a clique in the
strongly regular Cayley graph G_ell = Cay(F₁₁⁴, {d : Q2(d) non-square}), Q2(a,b,c,f) = c² − 2a² − bf
(eigenvalues 6710, 55, −66; Delsarte bound ω ≤ 102). Projectively, R is e4 plus k conics through e4 whose planes
share one tangent line at e4. Each clique vertex is 11 points, i.e. 22 graph vertices.

## 4. Files

- `hexgen.c` (copy of research/p4/d6/hexgen.c): H(q) for q = p, p², writes hex/hex_q11.bin (4 s).
- `tri.c`: the three-copy graph with surgeries, from RFILE/SFILE or greedy; bit-parallel BFS from all damaged and new
  vertices plus random sources (`RFILE=… SFILE=… ./tri hex/hex_q11.bin -1 SEED [out.edges]`).
- `build_d13D7.py`: **self-contained builder** (numpy only): rebuilds H(11) from Tits' equations with canonical
  point/line orders, σ = local duality on R (sorted order) and sorted order elsewhere, S = first |R| lines of the
  Hermitian spread, NS = circulant with offsets {0,1,3,7,15,26,40,56,77,101}; writes the apsp.c edge list (2 min).
- `apsp_par.c`: research/lifts/coordinator_check/apsp.c with the source batches in parallel (same checks).
- `tools/`: hexlib.py, oppcheck.c (independent pairwise-opposite check by BFS balls), povoid_ils.c,
  hermitian_spread.py.
- `sets/`: R sets as point coordinates (input of build_d13D7.py) and as hexgen indices.
- Squad material: research/squads/d13D7_r1/, research/squads/d13D7_r2/ (briefs, code, scoreboards).

## 5. Current best and checks

(filled in at the end of the session)

## 6. What failed or was not worth running

(filled in at the end of the session)
