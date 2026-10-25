# optimal-sat: what is proved (living summary)

Project brief: `BRIEF.md`. Lead session: Opus, branch `claude/optimal-sat-nx83w2`, started 2026-10-25.

Status keys: **proved** (written proof, checked here), **computed** (SAT/exhaustive, with the command to rerun),
**open**.

## 0. Upper bounds the wiki table does not have yet, from published theorems (proved)

The wiki's "lowest known upper bounds" table (read 2026-10-25 over plain http; same as CANDIDATES.md says) has
(15,3) = 422 and (7,5) = 3106. Both can be lowered with results that are already published:

- **N^b(15,3) ≤ 418.** A bipartite Moore graph of degree 15 and diameter 3 is the incidence graph of a projective
  plane of order 14 (Singleton), and there is none by Bruck–Ryser (14 ≡ 2 mod 4 and 14 is not a sum of two squares).
  A bipartite (Δ,3,−2)-graph needs Δ or Δ−2 to be a perfect square (Delorme, Jørgensen, Miller, Pineda-Villavicencio,
  JGT 61 (2009); also Corollary Q below); 15 and 13 are not squares. For defect ε < Δ a bipartite (Δ,3,−ε)-graph is
  regular (Prop. 3.1 of arXiv:1203.3588, citing the same JGT paper; Lemma 1 below proves the case ε = 2), so its
  sides are equal and ε is even. So ε ≥ 4.
- **N^b(7,5) ≤ 3104.** Feria-Purón and Pineda-Villavicencio, DAM 160 (2012), Prop. 6.4: N^b(Δ,D) ≤ M^b(Δ,D) − 6 for
  Δ ≥ 3 and 5 ≤ D ≤ 187, D ≠ 6. M^b(7,5) = 3110. The wiki colours the cell "Moore bound minus 6" but prints 3106
  (Moore minus 4); every other D ≥ 5 cell in the wiki table is exactly M^b − 6.

Every other cell of the wiki's upper-bound table (Δ ≤ 16, D ≤ 10) agrees with what the published theorems give.

## 1. Bipartite (k,3,−2)-graphs: reduction to an oriented graph and a weighing matrix (proved)

A bipartite (k,3,−2)-graph is a bipartite graph with maximum degree k, diameter 3 and 2(k²−k) vertices (two less than
the bipartite Moore bound). They exist for k = 3, 4 and for no 5 ≤ k ≤ 10 (Delorme et al. 2009). **k = 11 is the
first open case, and it is exactly the (11,3) cell: excluding it gives N^b(11,3) ≤ 218** (defect 3 is impossible by
regularity and parity, as above). Feria-Purón's PhD thesis (Newcastle, March 2015, Table 3.2; read from the Newcastle
repository, figshare file 54314375) still lists N(11,3,B) ≤ M − 2 as the best bound, and its table treats (15,3) as
≤ M (it does not use Bruck–Ryser there either).

Call the two sides points and lines.

**Lemma 1.** Such a graph is k-regular with k²−k points and k²−k lines. Every point x has exactly one other point
x* with two common lines; every other point shares exactly one line with x. x ↦ x* is a fixed-point-free involution,
the same holds for lines, and if x, x* share lines ℓ, ℓ' then ℓ' = ℓ*. So the vertex set splits into
m = k(k−1)/2 disjoint 4-cycles ("quads" {x, x*, ℓ, ℓ*}).

*Proof.* Diameter 3 and bipartite: any two points share a line. For a point x,
|X| − 1 ≤ Σ_{ℓ ∋ x} (deg ℓ − 1) ≤ k(k−1), and the same for lines. With |X| + |Y| = 2(k²−k), if |X| = k²−k+1 then
equality holds for every x: all degrees are k and any two points share exactly one line; counting pairs of points,
C(k²−k+1, 2) = (k²−k−1)·C(k,2), false. So |X| = |Y| = k²−k. If deg x ≤ k−1 the bound gives
k²−k−1 ≤ (k−1)², false for k ≥ 3, so every vertex has degree k. Then the k(k−1) walks x–ℓ–y cover the k²−k−1 other
points with exactly one point covered twice. Common-neighbour counts are symmetric, so x ↦ x* is an involution, and
the two common lines of x, x* have the two common points x, x*, so they are partners. ∎

**Lemma 2 (0 or 2).** For quads c ≠ d, the points of c and the lines of d span either no edge or two disjoint edges.

*Proof.* Let d = {q, q*, ℓ, ℓ*} and let a ∉ d be a point on ℓ. The k−1 lines L ≠ ℓ through a are not ℓ* (a ∉ ℓ ∩ ℓ*)
and not partners of ℓ*, so each meets ℓ* in one point, which is not q or q* (else a, q share ℓ and L). Two of these
k−1 lines meet ℓ* in the same one of its k−2 other points b, so a and b share two lines: b = a*. So a* ∈ ℓ*. ∎

**Theorem Q.** Label the two points and the two lines of each quad 0 and 1. Let Γ be the digraph on the m quads with
c → d when the points of c meet the lines of d, and let s(c,d) = +1 if point 0 of c is on line 0 of d, −1 otherwise.
Let A be the adjacency matrix of Γ and W the signed adjacency matrix. Then

  (2I + A)(2I + A)ᵀ = (2I + A)ᵀ(2I + A) = kI + 2J   and   WWᵀ = WᵀW = (k−2)I.

Conversely, a 0/1 matrix A with zero diagonal and a ±1-signing W of it with these identities give a bipartite
(k,3,−2)-graph. (Off-diagonal entries of the first identity force A_cd + A_dc ≤ 1, so Γ is oriented, and the diagonal
gives out- and in-degree k−2.)

*Proof.* In quad blocks the incidence matrix N has diagonal blocks J₂ and, by Lemma 2, off-diagonal blocks 0, I₂ or
the anti-diagonal X₂. Lemma 1 says NNᵀ = NᵀN = (k−2)I + (I_m ⊗ J₂) + J. Conjugate by P = I_m ⊗ H/√2 with
H = [[1,1],[1,−1]]: PJ₂P = diag(2,0), PI₂P = I₂, PX₂P = diag(1,−1), so PNP is (2I + A) ⊕ W and
P(NNᵀ)P = (kI + 2J) ⊕ (k−2)I. The converse is the same computation read backwards: NNᵀ = (k−2)I + I⊗J₂ + J says any two
points share a line (and the same for lines), which gives diameter 3. ∎

**Corollary Q.** det(2I+A)² = k^{m+1} and det(W)² = (k−2)^m, so m even ⇒ k is a square and m odd ⇒ k−2 is a square.
This is the Delorme et al. condition (k square forces m even, k−2 square forces m odd). For k = 11, m = 55 and W is
a weighing matrix W(55,9).

**Lemma Q2 (local structure).** Fix a vertex u of Γ with out-set O and in-set I (|O| = |I| = k−2) and let R be the
rest. Then there are no arcs inside O, inside I, or from I to O; every y ∈ R has exactly two out-neighbours in O and
exactly two in-neighbours in I; and y ↦ O ∩ out(y) is a bijection from R onto the 2-subsets of O (likewise for I).

*Proof.* The off-diagonal entries of Theorem Q say: adjacent vertices have no common out-neighbour and no common
in-neighbour; non-adjacent ones have exactly two of each. An arc x → x' in O makes x' a common out-neighbour of the
adjacent u, x; an arc inside I or from I to O makes a common in-neighbour of an adjacent pair. y ∈ R is not adjacent to
u, so it has two out-neighbours in O and two in-neighbours in I. If y ≠ y' had the same pair {x, x'}, then the
non-adjacent x, x' would have three common in-neighbours u, y, y'. Finally |R| = C(k−2, 2). ∎

So for k = 11 the problem is a 55-vertex oriented graph with a weighing-matrix signing, and Lemma Q2 fixes vertex 0, its
9 out-neighbours, its 9 in-neighbours and all 72 arcs from R to O.

## 2. Computations

See `logs/defect2_calibration.md` for timings. Encoders in `defect2/`:
- `enc_d3m2.py`: incidence matrix with Lemma 1 normal form (slow; for cross-checks only);
- `enc_grid.py`: Lemma 1 + base-quad grid normal form, optional lex-leader;
- `enc_quot.py`: Theorem Q (A only, or A + signs), Lemma Q2 normal form (`--nf2`), lex-leader (`--sym`).

Cross-checks: all three encoders give SAT for k = 3, 4 and UNSAT for k = 5, 6 (and the quotient encoder for
k = 5..9), matching the literature. For k = 9 the oriented graph A exists (A-only instance is SAT; its underlying
graph is strongly regular with parameters (36,14,4,6)); the weighing-matrix signing is what fails.
`lift_verify.py` rebuilds the k = 3, 4 graphs from (A, W) and checks degree, order and diameter 3 by BFS.

Certified (kissat DRAT proof, drat-trim VERIFIED; logs in `logs/`):
- k = 5, 6, 7, 8, 9: no (k,3,−2)-graph (A + signs, `--signs --sym --nf2`); k = 9 proof 20 MB, check 12 s.
- k = 10: not even the oriented graph A exists (`--sym --nf2`, A only): solve 216 s, proof 103 MB, check 1055 s.

Not Cayley: no Cayley digraph on Z₅₅ or Z₁₁ ⋊ Z₅ (the two groups of order 55) satisfies the A-conditions for
k = 11 (`cayley_search.py 11`); none on Z₃₆ for k = 9 either.

## 3. k = 11: status (open; partial computations)

The question "is there a bipartite (11,3,−2)-graph?" (equivalently: is N^b(11,3) ≤ 218?) is **not settled**.
- Monolithic A-only runs (`--sym --nf2 --ntt --alltr`, sha256 b6101044…): kissat 8.1 CPU-hours, CaDiCaL with a
  streamed LRAT check 6.9 CPU-hours, kissat on the signed instance about 4 CPU-hours; no answer
  (`logs/k11_monolithic.md`).
- Case split by the degree sequences (α, β) of B (the 9×9 block of arcs from O to I at vertex 0), with a choice
  rule for the base vertex. Under rule R1 (vertex 0 lies on the most directed triangles; 245,667 cubes):
  - **certified** (CaDiCaL + LRAT, lrat-check VERIFIED): 6 of the 8 cubes with t ≤ 3 directed triangles at
    vertex 0 (all with t ≤ 2, and 2 of the 4 with t = 3). The other two t = 3 cubes were stopped after about 55 min.
    See `logs/k11_lowt.log`.
  - Uncertified kissat runs, all UNSAT: B 3-regular (18 s), B 4-regular (195 s), α = β = (5,5,4,4,4,4,4,3,3)
    (225 s), and 22 of 23 random cubes (one timed out).
  - Costs and the alternative rule R2 are in `logs/defect2_calibration.md`.
- No Cayley digraph on either group of order 55 satisfies the A-conditions (complete search).
- Ready for a cluster: `defect2/setup_worker.sh` and `defect2/worker.sh` (estimate 10²–10⁴ CPU-hours, dominated by
  low-t, flat-α cubes). Request: `research/squads/requests/2026-10-25T0915-optimal-sat-k11-cubes.md`.
