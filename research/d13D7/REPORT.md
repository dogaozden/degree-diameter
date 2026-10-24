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

| R | order | check |
|---|---|---|
| 320 (fibration, r1 c8) | 1,063,576 | checks/d13D7_hex11_R320_n1063576.check.txt (all-pairs VALID) |
| **397** (LNS, r2 c6) | **1,063,730** | checks/d13D7_hex11_R397_n1063730.check.txt (all-pairs VALID) |

The 397 set: research/d13D7/sets/R397_r2c6_idx.txt / _coords.txt. Build with `python3 build_d13D7.py
sets/R397_r2c6_coords.txt out.edges` (numpy only, independent of hexgen.c) or from the d7hex solution
research/frontier/sols/d13D7_hex11_R397_n1063730.sol with `d7hex edges` (research/squads/exp2/hexd7/d7hex.c); both give
the same edge set (checked edge by edge). All-pairs: apsp_wide.c (apsp.c with 512 sources per batch; checked against
apsp.c on smaller graphs), 13-regular, bipartite, diameter exactly 7.

How 397 arose (squad round 2, card c6, research/squads/d13D7_r2/c6/lns.c): the 320 set was maximal but not
1-swap optimal. e4 was the only point of R orthogonal to 90 points at infinity (x0 = 0); removing e4 freed them and 62
are pairwise opposite (381). The LNS (remove a block of R, exact maximum pairwise-opposite subset of the freed
candidates, accept if not smaller) then reached 397 and plateaued. Round 3 (research/squads/d13D7_r3) attacked the
plateau: see research/squads/LOG.md.

## 6. What failed or was not worth running

- Haar/Cayley search (first-moment ceiling, §1). Not run.
- Four copies, twisted lifts, a dual copy H(11)^D in the cycle: a 3-cycle of copies always has one H -> H
  transition, so the local duality cannot be made global for q = 11.
- Larger cliques of the fibration graph (r2 c1, c3, c5: 29 is the most ever seen; 39,089 distinct 29-cliques),
  the square-class direction (20 lines), two-direction fibrations (r2 c2).
- Relaxed surgery with distance-4 pairs in R. The theorem extends (R non-collinear, σ(R) non-concurrent, and the
  "middle" structure of R mirrored by σ(R)), and on the point side large structured R exist: around a point p the
  points at distance 4 map onto the GQ Q(4,q) = p^perp/p, and an ovoid of that GQ gives 121 stars of 11 points
  (1,331 points). But the line side must have the same stars, and for lines of H(11) the "forbidden" choices are
  not coherent (relax/cohere.c, cohere3.c: 110-121 distinct pairs where coherence would give 11; points give 11).
  The line-star search reached 128 lines (r2 c8). Closed for q = 11 (open for q = 3^h, where H(q) is self-dual).
- Orbit unions beyond order 44 (r2 c4: 55 -> 362, 110 -> 340, 61 -> 256), LNS from the orbit set (rigid), crossover.

## 7. The same surgery at other q, and with more copies

**Other q, three copies (Δ = q+2).** Nothing in §2 depends on q = 11:
- (7,7): 23,436 + 2·58 = **23,552** (partial ovoid of Q(6,5) from povoid_ils); (9,7): 117,648 + 2·172 = **117,992**
  (Q(6,7)); checks/d7D7_hex5_R58_n23552.check.txt, d9D7_hex7_R172_n117992.check.txt (apsp.c, D-1 fails).
- (11,7), q = 9: Q(6,9) has ovoids; one is a union of 10 orbits of an element of order 73 (q9/orb73.py: since all
  subgroups of order 73 of O(7,9) are conjugate and the dual of the Hermitian spread is invariant under one, a union
  of 73-orbits must exist), with the Hermitian spread: 398,580 + 2·730 = **400,040** (checks/d11D7_hex9_R730_n400040).
- (11,7) with an explicit duality: H(q) is self-dual exactly for q = 3^h. For q = 9 the Plücker vectors of the lines
  span the 14-dim Lie algebra g2 inside Λ²V; its invariant form has a 7-dim radical in characteristic 3 and the
  quotient sends every line to a point, every pencil to a line (q9/plucker.py, dualmap.py); a similitude ψ found by
  matching an apartment (findpsi.py) carries this onto H(9): an explicit duality δ, verified on all 66,430 points and
  lines (duality9.py, q9/dual_pt2line.txt). With σ = δ the local duality holds at EVERY point, so R only has to be
  non-collinear (at most q^4+q^2+1 = 6,643): tools/ncol_ils.c finds 3,859, hub graph random 8-regular with same-side
  distances <= 6 (tools/hubgraph.py), builder tri_dual.c: 398,580 + 2·3,859 = **406,298** (all-pairs VALID).

**More copies (Δ = q+1+r, 2r+1 copies; the table's (12,7), (14,7), (15,7), (16,7)).** Levels Z_{2r+1}, matchings
(p, i) ~ (σ(p), i+k) for k = 1..r. Any two levels differ by ±k for some k <= r, and the pair of levels i, i+k with the
k-th matching is exactly the three-copy situation, so the base construction has diameter 7 for any σ and the
surgery proof applies verbatim pair by pair. Freeing r ∈ R at all levels frees r slots at each (r, i) and r at each
(σ(r), i): r line-side and r point-side hubs, +2r vertices per point; hub degree <= q - r. multi.c builds these
(tested all-pairs: 5 copies of H(5) with 8 points, 39,092; 7 copies of H(7), r = 3, 11 points, 274,578).
Candidates (checks in progress at the time of writing; see §8):
(12,7) 664,300 + 4·1,953 = 672,112 (q = 9, σ = δ, hub graph = incidence graph of H(5), degree 6, diameter 6);
(14,7) 1,771,560 + 4·397 = 1,773,148; (15,7) 2,480,184 + 6·397 = 2,482,566 (q = 11, R = the 397 set);
(16,7) 4,022,340 + 4·168 = 4,023,012 (q = 13, R = 168 points of Q(6,13) from povoid_ils).
For these graphs (x, i) -> (x, i+1) (hubs fixed) is an automorphism, so BFS from level 0 and all hubs gives the
exact diameter (apsp_src.c); the coordinator may prefer full all-pairs.

## 8. Status of the multi-copy checks

(filled in below as they finish)
