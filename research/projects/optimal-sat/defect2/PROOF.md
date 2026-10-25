# Bipartite (k,3,−2)-graphs: the reduction behind the SAT instances, in full

This file is written so that a mathematician can check every step. The short version is in `../SUMMARY.md` §1.

**Definition.** A bipartite (k,3,−2)-graph (k ≥ 3) is a bipartite graph G of maximum degree k and diameter at most 3
with 2(k² − k) vertices. (The bipartite Moore bound for diameter 3 is 2(k² − k + 1).) Call the two colour classes
X ("points") and Y ("lines"); write p ∈ ℓ for adjacency, c(x, x') for the number of common neighbours.

## 1. Structure

**Lemma 1.** |X| = |Y| = k² − k, every vertex has degree k, and for every point x there is exactly one point
x* ≠ x with c(x, x*) = 2, while c(x, x') = 1 for every other point x' ≠ x. The map x ↦ x* is a fixed-point-free
involution of X. The same holds for lines. If ℓ, ℓ' are the two common lines of x and x*, then ℓ' = ℓ*.

*Proof.* G is bipartite with diameter ≤ 3, so two vertices of the same class are at distance 2: c(x, x') ≥ 1 for all
points x ≠ x' (and likewise for lines). Fix a point x. Every other point is a neighbour of a neighbour of x, so
|X| − 1 ≤ Σ_{ℓ ∋ x} (deg ℓ − 1) ≤ deg(x)(k − 1) ≤ k(k − 1),  hence |X| ≤ k² − k + 1, and the same for Y.
Since |X| + |Y| = 2(k² − k), either both equal k² − k, or one of them, say X, has k² − k + 1 points and Y has
k² − k − 1 lines. In the second case all the inequalities are equalities for every x: deg x = k, all lines through x
have degree k, and the k(k − 1) walks x–ℓ–x' reach every other point exactly once, i.e. c(x, x') = 1 for all x ≠ x'.
Every line lies on some point (G is connected, as its diameter is finite), so every line has degree k. Counting
pairs of points with their common line: C(|X|, 2) = Σ_ℓ C(k, 2) = |Y|·C(k, 2), i.e.
(k² − k + 1)(k² − k) = (k² − k − 1)·k(k − 1), which is false. So |X| = |Y| = k² − k.
Now k² − k − 1 ≤ deg(x)(k − 1). If deg x ≤ k − 1 this gives k² − k − 1 ≤ (k − 1)², i.e. k ≤ 2, false. So
deg x = k for every point, and likewise for every line. The multiset of endpoints of the k(k − 1) walks x–ℓ–x'
(x' ≠ x) has size k(k − 1) = (k² − k − 1) + 1 and covers each of the k² − k − 1 other points at least once, so exactly
one point x* is covered twice (c(x, x*) = 2) and every other point once. Since c is symmetric, (x*)* = x. Finally
the two common lines ℓ, ℓ' of x and x* have the two common points x, x*, so c(ℓ, ℓ') = 2 and ℓ' = ℓ*. ∎

Consequently the vertex set splits into m = k(k − 1)/2 disjoint "quads" {x, x*, ℓ, ℓ*} with all four incidences
present; call a quad's points and lines its own. Two points of different quads share exactly one line; two lines of
different quads share exactly one point; the two points of a quad share exactly their two own lines.

**Lemma 2 (0 or 2).** Let c ≠ d be quads. The points of c and the lines of d span either no edge or two disjoint
edges (each point of c on exactly one line of d, each line of d through exactly one point of c).

*Proof.* Let d = {q, q*, ℓ, ℓ*} and let a be a point on ℓ that is not in d. Consider the k − 1 lines L ≠ ℓ through
a. None of them is ℓ* (otherwise a ∈ ℓ ∩ ℓ* = {q, q*}), and none is the partner of ℓ* (that is ℓ), so each L meets
ℓ* in exactly one point. That point is neither q nor q*: if q ∈ L then a and q share the two lines ℓ and L, so
a = q* or a = q, i.e. a ∈ d. So the k − 1 lines L meet ℓ* in its k − 2 points other than q, q*; by pigeonhole two of
them meet ℓ* in the same point b, and then c(a, b) ≥ 2, so b = a*. Hence: if a point a of a quad c lies on ℓ, then
a* lies on ℓ*. A point lies on at most one of ℓ, ℓ* (they share only q, q*), and a, a* are not both on ℓ (they
share only their own lines). This gives the claim. ∎

Also, for c ≠ d at most one of "points of c meet lines of d" and "points of d meet lines of c" holds: the four pairs
(p, q) with p ∈ c, q ∈ d each have exactly one common line; an edge from a point p of c to a line of d makes that
line the common line of p with both points of d, and an edge from a point of d to a line of c makes it the common line
of that point with both points of c; two such edges would give a pair (p, q) two common lines.

## 2. The quotient (Theorem Q)

Label the two points of each quad 0, 1 and the two lines 0, 1. Define the digraph Γ on the set of quads by c → d
iff the points of c meet the lines of d, and the sign s(c, d) = +1 if point 0 of c is on line 0 of d (then point 1
of c is on line 1 of d), s(c, d) = −1 otherwise. Let A be the 0/1 adjacency matrix of Γ and W the signed one
(W_cd = s(c, d) if c → d, else 0).

**Theorem Q.** (2I + A)(2I + A)ᵀ = (2I + A)ᵀ(2I + A) = kI + 2J and WWᵀ = WᵀW = (k − 2)I.
Conversely, a 0/1 matrix A with zero diagonal and a matrix W with W_cd ∈ {±1} where A_cd = 1 and W_cd = 0 where
A_cd = 0, satisfying these identities, define a bipartite (k,3,−2)-graph.

*Proof.* Order points and lines quad by quad. By Lemma 2 the point–line incidence matrix N consists of 2×2 blocks:
J₂ (all ones) on the diagonal, and off the diagonal I₂ if s(c,d) = +1, X₂ = [[0,1],[1,0]] if s(c,d) = −1, 0 if
c ↛ d. Lemma 1 says exactly NNᵀ = (k − 2)I + (I_m ⊗ J₂) + J and NᵀN = (k − 2)I + (I_m ⊗ J₂) + J (diagonal k,
partners 2, all other pairs 1). Let H = [[1,1],[1,−1]] and P = I_m ⊗ H/√2 (orthogonal, P = Pᵀ = P⁻¹). Then
H J₂ H/2 = diag(2, 0), H I₂ H/2 = diag(1, 1), H X₂ H/2 = diag(1, −1). So, after reordering coordinates into "first
of each pair" and "second of each pair", PNP = (2I + A) ⊕ W, P(I ⊗ J₂)P = 2I ⊕ 0 and PJP = 2J ⊕ 0. Conjugating
the two identities for N by P gives (2I + A)(2I + A)ᵀ = (k − 2)I + 2I + 2J = kI + 2J and WWᵀ = (k − 2)I, and the
same for the transposed products. The converse: given (A, W), N := P((2I + A) ⊕ W)P is the 0/1 block matrix above,
and the identities say NNᵀ = NᵀN = (k − 2)I + I⊗J₂ + J: every point is on k lines, any two points share a line,
any two lines share a point. Then any point p and line ℓ are at distance ≤ 3 (take a point q on ℓ; p, q share a
line), so the bipartite graph has diameter ≤ 3, degree k and 2·2m = 2(k² − k) vertices. ∎

Reading off entries (c ≠ d):
- diagonal of (2I + A)(2I + A)ᵀ: 4 + outdeg(c) = k + 2, so every vertex of Γ has out-degree k − 2 (in-degree from
  the other product);
- off-diagonal: 2(A_cd + A_dc) + |O(c) ∩ O(d)| = 2, where O(c) is the out-neighbourhood; so A_cd + A_dc ≤ 1
  (Γ is oriented), **adjacent vertices have no common out-neighbour, non-adjacent vertices have exactly two**; the
  same with in-neighbourhoods from (2I + A)ᵀ(2I + A);
- WWᵀ off-diagonal: for non-adjacent c, d with common out-neighbours e₁, e₂, s(c,e₁)s(d,e₁) + s(c,e₂)s(d,e₂) = 0.

**Corollary Q.** det(2I + A)² = det(kI + 2J) = k^{m−1}(k + 2m) = k^{m+1} and det(W)² = (k − 2)^m. So if m is even
then k is a square, and if m is odd then k − 2 is a square. (This is Delorme–Jørgensen–Miller–Pineda-Villavicencio's
"k or k − 2 is a square".) For k = 11, m = 55 and W is a weighing matrix W(55, 9).

## 3. Normal form used by the encoder (`enc_quot.py --nf2`)

**Lemma Q2.** Let u be a vertex of Γ, O = O(u), I = I(u) (in-neighbourhood), R = the other m − 1 − 2(k − 2) vertices.
(a) There is no arc inside O, inside I, or from I to O. (b) Every y ∈ R has exactly two out-neighbours in O and
exactly two in-neighbours in I. (c) y ↦ O(y) ∩ O is a bijection from R onto the 2-subsets of O (and y ↦ I(y) ∩ I onto
the 2-subsets of I).

*Proof.* (a) x → x' with x, x' ∈ O: x' is a common out-neighbour of the adjacent pair u, x. z → z' with z, z' ∈ I:
z is a common in-neighbour of the adjacent pair u, z'. z → x with z ∈ I, x ∈ O: z is a common in-neighbour of the
adjacent pair u, x. (b) y ∈ R is not adjacent to u, so it has exactly two common out-neighbours with u (which lie in
O) and two common in-neighbours (in I). (c) If y ≠ y' in R had O(y) ∩ O = O(y') ∩ O = {x, x'}, then x, x' (not
adjacent, by (a)) would have the three common in-neighbours u, y, y'. And |R| = C(k − 2, 2). ∎

So we may label: vertex 0 = u, O = {1, …, k − 2}, I = {k − 1, …, 2k − 4}, and R = the pairs {i, j} ⊂ O in
lexicographic order, with y_{ij} → i, j and no other arcs between R and O (unit clauses in the CNF).

## 4. What the CNF says, and why each part is sound

Variables a[c][d] (c ≠ d) mean c → d. Clauses:
1. normal form (Lemma Q2 and the labelling just described): unit clauses;
2. ¬a[c][d] ∨ ¬a[d][c] (Γ oriented);
3. out-degree and in-degree exactly k − 2 (sequential counters);
4. for every pair c < d and each direction: auxiliary y_e ↔ a[c][e] ∧ a[d][e] (resp. a[e][c] ∧ a[e][d]); a counter
   over the y_e with outputs "≥ 1", "≥ 2", "≥ 3" defined by full equivalences; clauses ¬(≥3),
   adj → ¬(≥1), ¬adj → (≥2), where adj ↔ a[c][d] ∨ a[d][c]. This is exactly the off-diagonal condition of §2;
5. `--ntt`: ¬(a[p][q] ∧ a[p][r] ∧ a[q][r]) for all distinct p, q, r — implied by item 4 (q, r would be adjacent with
   the common in-neighbour p), added only for propagation;
6. `--sym` (lex-leader): for each generator π of the group of relabellings that fix the normal form — transpositions
   of two elements of O (acting on R through the pair labels) and transpositions of two elements of I — clauses saying
   that the assignment is lexicographically ≤ its image under π, in the fixed row-major order of the a-variables.
   Every solution can be relabelled into normal form and then replaced by the lexicographically smallest member of
   its orbit under that group, which satisfies all these clauses; so they remove no isomorphism class.
7. `--signs` only: variables s[c][d] and, for every non-adjacent pair, the clauses forcing the two sign products to
   differ (the WWᵀ condition); a gauge fix: s = +1 on the arcs 0 → x (x ∈ O), z → 0 (z ∈ I), on the first arc from
   each y ∈ R into O and on the first arc into each y ∈ R from I. Changing the labels inside a quad multiplies a row
   (or column) of W by −1; the fixed arcs form a forest in the bipartite row/column graph, so every solution can be
   gauged to satisfy the fix without changing A, hence without touching the lex-leader clauses.

So UNSAT of the A-only CNF (items 1–6) implies that no bipartite (k,3,−2)-graph exists.

Checks of the encoder against known results: SAT for k = 3, 4 (the two known graphs; `lift_verify.py` rebuilds them
from (A, W) and checks degree, order and diameter by BFS); UNSAT for k = 5..10 (Delorme et al.); for k = 9 the A-only
instance is SAT and the signing fails, consistent with their non-existence proof for Δ = 9.
