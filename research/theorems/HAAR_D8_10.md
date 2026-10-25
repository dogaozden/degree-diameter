# Haar graphs of diameter 8, 9 and 10: what is proved and what is computed

Doğa Özden's degree–diameter lab, with Claude Code (job `thm-haar`, 2026-10-25). Written for Gabriela Araujo-Pardo
and Ignacio López. Draft; corrections welcome.

**Labels.** Every statement below carries one of three labels.

- **Theorem, Proposition, Lemma, Corollary**: complete proof in this note, or a cited standard result named in place
  (marked *cited*).
- **Computer-checked**: a statement about one explicit graph, verified by programs. The programs and their logs are
  named. Some of these graphs also have a Lean 4 proof (kernel-checked, standard axioms only).
- **Heuristic**: a model or a measurement that guided the search. It is not used in any proof.

**The main point, stated plainly.** None of the records at D = 8, 9, 10 comes from a general theorem. Each record is one
explicit graph (a Haar graph H(G, S) in 33 of the 34 cells), found by computer search and checked by computer. What
this note proves is:

1. the criterion that makes those checks exact (§2): two breadth-first searches, from (e, A) and (e, B), decide the
   diameter of a Haar graph, and the diameter is a covering statement about products of S and S⁻¹ in G;
2. the structural facts behind the orbit-closed connection sets that the search used (§3);
3. general upper bounds and a few exact counting facts (§4).

The records table is in §5, prior art in §6, and the commands to re-check everything in §7.

## Contents

0. Summary of statements
1. Setting and notation
2. The covering criterion, and why the symmetric checks are exact
3. Orbit-closed connection sets
4. Counting bounds and family statements
5. Records at D = 8, 9, 10
6. Prior art, and what is ours
7. How to re-check

---

## 0. Summary of statements

| # | statement | label |
|---|---|---|
| Lemma 1.2 | H(G,S) is bipartite, simple, Δ-regular, of order 2\|G\|; right translations act regularly on each side | Lemma |
| Lemma 2.1 | the diameter is the largest eccentricity over one vertex from each orbit of any automorphism group | Lemma |
| Prop. 2.2 | distances from (e,A) and (e,B) are word lengths in S and S⁻¹ | Proposition |
| Cor. 2.3 | diam H(G,S) = max(ecc(e,A), ecc(e,B)) | Corollary |
| Thm. 2.4 | covering criterion: D = 2k needs S(S⁻¹S)^(k−1) = G; D = 2k+1 needs (S⁻¹S)^k = G and (SS⁻¹)^k = G | Theorem |
| Lemma 2.5 | an edge-preserving bijection of a finite graph is an automorphism (used by the level-shift checker) | Lemma |
| Lemma 3.1 | H(G,S) ≅ H(G, a·ψ(S)^(±1)·b) for a, b ∈ G, ψ ∈ Aut(G) | Lemma |
| Prop. 3.3 | if α(S) = S, then α acts on H(G,S) fixing (e,A), (e,B); every uncovered set is a union of α-orbits | Proposition |
| Prop. 3.4 | an involution in the symmetry group forces word coincidences on at least \|G\|/\|Fix\| elements; odd order avoids this | Proposition |
| §3.5 | why orbit-closed S makes larger groups searchable | Heuristic, measured |
| Thm. 4.1 | \|G\| ≤ Σ_{j<D} (Δ−1)^j (the bipartite Moore bound, per side); strict for D = 8, 9, 10 and Δ ≥ 3 | Theorem (strictness cited) |
| Thm. 4.3 | \|G/G′\| ≤ A(Δ,D), a polynomial in D for fixed Δ | Theorem |
| Cor. 4.4 | the same for abelian groups, for Q × Z_n with Q perfect, and for metacyclic groups | Corollary |
| Prop. 4.5 | at odd D, the binding words hitting an involution come in pairs | Proposition |
| §5 | 34 cells at D = 8, 9, 10 where our graph is larger than the 2013 table | Computer-checked (12 also in Lean, at the record or at an earlier value) |

---

## 1. Setting and notation

### 1.1 The problem

N^b(Δ, D) is the largest order of a bipartite graph with maximum degree at most Δ and diameter at most D. The bipartite
Moore bound is

$$N^b(\Delta,D) \le M^b(\Delta,D) = 2\sum_{j=0}^{D-1}(\Delta-1)^j .$$

"The table" means Table 4 of M. Miller and J. Širáň, *Moore graphs and beyond: a survey of the degree/diameter
problem*, Electron. J. Combin. Dynamic Survey DS14v2 (2013), which the Combinatorics Wiki reproduces. At D = 8, 9, 10
the wiki values equal the survey values (checked against the live wiki page on 2026-10-25,
`research/projects/table-audit/AUDIT.md` §1 on branch `claude/table-audit-1odopy`).

### 1.2 Haar graphs

**Definition 1.1.** Let G be a finite group with identity e and order N, and let S ⊆ G with |S| = Δ. The *Haar graph*
H(G, S) has vertex set G × {A, B}, and (g, A) is adjacent to (sg, B) for every g ∈ G and s ∈ S.

*Conventions.* Some authors join (g, A) to (gs, B). The map (g, X) ↦ (g⁻¹, X) is an isomorphism from our H(G, S) to
that graph built with S⁻¹, and H(G, S⁻¹) ≅ H(G, S) by Lemma 3.1(iv), so the two conventions give isomorphic graphs.
H(G, S) is also the regular G-cover (derived graph) of the dipole with Δ parallel edges carrying the voltages s ∈ S.
For G = Z_n these are the cyclic Haar graphs of Hladnik, Marušič and Pisanski. All our files and checkers use the
left convention of Definition 1.1 (`research/frontier/build_haar2.py`, header; `lean/BipartiteDD/Haar/GraphD.lean`,
where `inl g ~ inr h` iff `h * g⁻¹ ∈ S`).

For h ∈ G let ρ_h be the right translation ρ_h(g, X) = (gh, X).

**Lemma 1.2.** Let |S| = Δ ≥ 1.

(a) H(G, S) is bipartite with parts G × {A} and G × {B}, simple, Δ-regular, and has 2N vertices.

(b) Each ρ_h is an automorphism, and {ρ_h : h ∈ G} acts regularly (transitively, with trivial stabilisers) on each part.

(c) H(G, S) is connected if and only if S⁻¹S generates G.

*Proof.* (a) Edges join the two parts by definition. The neighbours of (g, A) are (sg, B), s ∈ S, and sg = s′g forces
s = s′, so there are exactly Δ of them. The neighbours of (h, B) are (s⁻¹h, A), s ∈ S, again Δ distinct vertices.

(b) If (g, A) ~ (sg, B) then (gh, A) ~ (sgh, B), so ρ_h maps edges to edges; its inverse is ρ_{h⁻¹}. On G × {X},
ρ_h(e, X) = (h, X), and ρ_h fixes a vertex only if h = e.

(c) By Proposition 2.2 below, the A-vertices joined to (e, A) by a walk are the (x, A) with x in the union of the sets
(S⁻¹S)^j, j ≥ 0. That union contains e and is closed under products, so in the finite group G it is the subgroup
generated by S⁻¹S. Every B-vertex (h, B) is adjacent to the A-vertex (s⁻¹h, A). So the graph is connected iff that
subgroup is G (use (b) to move any vertex to (e, A) or (e, B)). ∎

### 1.3 Words

For X, Y ⊆ G write XY = {xy : x ∈ X, y ∈ Y}, X⁻¹ = {x⁻¹ : x ∈ X}, X⁰ = {e} and X^j = X·X^(j−1). Since
e ∈ S⁻¹S, we have (S⁻¹S)^i ⊆ (S⁻¹S)^j for i ≤ j, and likewise for SS⁻¹.

An *A-word* of length L is a sequence (t_1, …, t_L) of letters t_i ∈ S, with value

$$w(S) = \cdots\, t_4^{-1}\, t_3\, t_2^{-1}\, t_1 \qquad(\text{signs } +,-,+,-,\dots \text{ read from the right}).$$

A *B-word* has the opposite signs: w(S) = ⋯ t_3⁻¹ t_2 t_1⁻¹. A word is *reduced* if t_{i+1} ≠ t_i for all i. There are
Δ(Δ−1)^(L−1) reduced words of each kind and length L ≥ 1. Walks in H(G, S) that start at (e, A) correspond exactly to
A-words, and a walk backtracks exactly when its word is not reduced (Proposition 2.2).

Throughout, ℓ = D − 1 and

$$W(\Delta,D)=\sum_{j=0}^{D-1}(\Delta-1)^j = \tfrac12 M^b(\Delta,D).$$

### 1.4 The groups

- SL(2, q), PSL(2, q) = SL(2, q)/{±I} and PGL(2, q) = GL(2, q)/(scalars), of orders q(q² − 1), q(q² − 1)/gcd(2, q − 1)
  and q(q² − 1). For q = p^e with e > 1 the field is GF(p)[x]/(f), with f named in the file (for example
  `sl 25 poly x^2+2`); a field element c_0 + c_1 x + ⋯ is written as the integer c_0 + c_1 p + ⋯.
- Direct products Q × Z_n and Q_1 × Q_2 × Z_n with Q, Q_i of the types above (file spec `prod Q1 Q2 n <n>`).
- Metacyclic groups Z_m ⋊_r Z_k: pairs (a, j) ∈ Z_m × Z_k with (a, j)(b, l) = (a + r^j b, j + l), where r^k ≡ 1 (mod m).
  The order is mk.

*File format* (`research/frontier/sols/*.txt`). The header is `Δ D <group> n <n> N <|G|>`, then Δ lines
`<index> mat(a,b,c,d) z=Z` for the element ([[a, b], [c, d]], Z) of Q × Z_n (`prod[mat(…);mat(…)] z=Z` for products,
`meta(a=…,j=…)` for metacyclic groups; the index is the search program's own and is ignored by the checkers). The first
listed element is e in every file; by Lemma 3.1 this is no loss of generality.

---

## 2. The covering criterion, and why the symmetric checks are exact

This section is what a referee needs in order to trust the record checks. Every check of a Haar graph in §5 computes
the eccentricities of exactly two vertices, (e, A) and (e, B). Lemma 2.1 and Lemma 1.2(b) say why that gives the
diameter, and Theorem 2.4 says what is being verified in group-theoretic terms.

For a vertex v of a graph X, ecc(v) = max_u d(v, u), with d(v, u) = ∞ if there is no path. diam X = max_v ecc(v).

**Lemma 2.1 (orbit representatives).** Let Γ be a group of automorphisms of a finite graph X, and let R be a set of
vertices that meets every Γ-orbit. Then diam X = max_{r ∈ R} ecc(r).

*Proof.* "≥" is clear. Let u, v be vertices. Choose γ ∈ Γ and r ∈ R with γ(u) = r. Automorphisms preserve distances,
so d(u, v) = d(γu, γv) = d(r, γv) ≤ ecc(r). ∎

**Proposition 2.2 (distances from the two base vertices).** Let S ≠ ∅. For x ∈ G and j ≥ 0:

| statement | condition |
|---|---|
| d((e,A), (x,A)) ≤ 2j | x ∈ (S⁻¹S)^j |
| d((e,A), (x,B)) ≤ 2j + 1 | x ∈ S(S⁻¹S)^j |
| d((e,B), (x,B)) ≤ 2j | x ∈ (SS⁻¹)^j |
| d((e,B), (x,A)) ≤ 2j + 1 | x ∈ S⁻¹(SS⁻¹)^j |

*Proof.* A walk of length L from (e, A) passes through (g_0, A), (g_1, B), (g_2, A), … with g_0 = e,
g_i = t_i g_{i−1} for odd i and g_i = t_i⁻¹ g_{i−1} for even i, where t_i ∈ S is the letter used at step i. Every choice
of letters gives a walk. So the endpoints of the walks of length exactly 2j are the vertices (x, A) with
x ∈ (S⁻¹S)^j, and those of length exactly 2j + 1 are the (x, B) with x ∈ S(S⁻¹S)^j. If d((e, A), (x, A)) = 2i ≤ 2j,
a shortest path followed by j − i back-and-forth steps along one edge is a walk of length exactly 2j; conversely a walk
of length 2j bounds the distance by 2j. The same holds for odd lengths. From (e, B) the first step goes to (t_1⁻¹, A),
the second to (t_2 t_1⁻¹, B), and so on, which gives the last two rows. The walk backtracks at step i + 1 exactly when
t_{i+1} = t_i, i.e. when its word is not reduced. ∎

**Corollary 2.3 (two sources suffice).** diam H(G, S) = max(ecc(e, A), ecc(e, B)).

*Proof.* Lemma 2.1 with Γ = {ρ_h} and R = {(e, A), (e, B)}, which meets both orbits by Lemma 1.2(b). ∎

**Theorem 2.4 (covering criterion).** Let S ≠ ∅ and D ≥ 2.

(a) If D = 2k, then diam H(G, S) ≤ D if and only if S(S⁻¹S)^(k−1) = G.

(b) If D = 2k + 1, then diam H(G, S) ≤ D if and only if (S⁻¹S)^k = G and (SS⁻¹)^k = G.

*Proof.* (a) Suppose diam ≤ 2k. For x ∈ G, d((e, A), (x, B)) is odd (the graph is bipartite) and at most 2k, hence at
most 2(k − 1) + 1, so x ∈ S(S⁻¹S)^(k−1) by Proposition 2.2. Conversely, suppose S(S⁻¹S)^(k−1) = G. Then
d((e, A), (x, B)) ≤ 2k − 1 for every x, and applying ρ_g, d((g, A), (h, B)) = d((e, A), (hg⁻¹, B)) ≤ 2k − 1 for all
g, h. Fix s ∈ S. For two A-vertices, (g′, A) is adjacent to (sg′, B), so d((g, A), (g′, A)) ≤ d((g, A), (sg′, B)) + 1
≤ 2k. For two B-vertices, (h′, B) is adjacent to (s⁻¹h′, A), so d((h, B), (h′, B)) ≤ d((s⁻¹h′, A), (h, B)) + 1 ≤ 2k.

(b) Suppose diam ≤ 2k + 1. Distances between vertices on the same side are even, hence at most 2k, so
(S⁻¹S)^k = G and (SS⁻¹)^k = G by Proposition 2.2. Conversely, if both hold, then by Proposition 2.2 and ρ_g all
same-side distances are at most 2k. For (g, A) and (h, B), (g, A) is adjacent to (sg, B), so
d((g, A), (h, B)) ≤ 1 + d((sg, B), (h, B)) ≤ 2k + 1. ∎

*Remarks.*

1. In terms of reduced words (Proposition 2.2): for D = 2k every x ∈ G must be the value of a reduced A-word of odd
   length ≤ D − 1; for D = 2k + 1 every x must be the value of a reduced A-word of even length ≤ D − 1 **and** of a
   reduced B-word of even length ≤ D − 1. These are the "binding words". Their number, W(Δ, D), is computed in §4.
2. At even D a single search from (e, A) decides the diameter. The checkers run both searches at every D; that is
   more than needed and is exact by Corollary 2.3.
3. At odd D the second condition is the first one for S⁻¹. If some ψ ∈ Aut(G) and a ∈ G satisfy ψ(S) = aS⁻¹, then
   ψ(S)⁻¹ψ(S) = SS⁻¹, so ψ maps (S⁻¹S)^k onto (SS⁻¹)^k and the two conditions are equivalent. (If ψ(S) = S⁻¹a, then
   ψ maps (S⁻¹S)^k onto a⁻¹(SS⁻¹)^k a, with the same conclusion.) For abelian G, ψ = inversion always works. No checker
   uses this.
4. The sufficiency directions of (a) and (b) are formalised in Lean as `haar_ediam_le_even` and `haar_ediam_le_odd`
   (`lean/BipartiteDD/Haar/GraphD.lean`). The Lean record proofs supply, for every x ∈ G, an explicit word; the kernel
   checks the words (`decide +kernel`, no `native_decide`).

**Lemma 2.5 (edge-preserving bijections).** Let X be a finite graph and φ a bijection of its vertex set that maps every
edge to an edge. Then φ is an automorphism.

*Proof.* φ induces an injective map from the finite edge set to itself, which is therefore a bijection. So every edge
is the image of an edge, and φ⁻¹ also maps edges to edges. ∎

This is what the level-shift checker `apsp_orb.c` relies on: it verifies edge by edge that a cyclic shift of the
vertex labels maps edges to edges, and then runs BFS from one vertex per orbit (Lemma 2.1). No D = 8–10 record in §5
depends on it; it is used for the D = 7 cover graphs.

### 2.6 What each checker computes, and which statement makes it exact

| program | written independently of the search? | what it does | exact because of |
|---|---|---|---|
| `research/frontier/build_haar2.py` | yes | builds the field from addition/multiplication tables and checks associativity, distributivity and commutativity on 20,000 random triples and every inverse; enumerates SL/PSL/PGL(2, q) by brute force over all (a, b, c, d) and checks the order against the formula; builds the Δ permutations g ↦ sg of G and checks each is a permutation; BFS from (e, A) and from (e, B); requires every vertex reached within D, maximum degree Δ, no repeated edge; prints the sha256 of the edge list | Lemma 1.2, Cor. 2.3 |
| `research/frontier/check_haar_indep.py` | yes (its own field, matrix and enumeration code) | same two searches | Cor. 2.3 |
| `research/frontier/haarcheck_sl.c`, `research/frontier/haarcheck2.c` | yes (two separate C programs) | G = SL(2, p) × Z_n, p prime only; own indexing of SL(2, p), explicit 2 × 2 products mod p, inverse generators computed as [[d, −b], [−c, a]] and −z; bitset BFS from (e, A) and (e, B), about 4–6 bits of memory per group element | Cor. 2.3 |
| `research/structured/tools/haarcheck_psl.c` | yes | the same for PSL(2, p) × Z_n, p an odd prime | Cor. 2.3 |
| `research/theorems/haar_d8_10/hc_factor.c` | yes (written for this note) | SL(2, p) or PSL(2, p) times Z_n, p prime: permutation tables of the matrix factor (§5.3), then the same two searches | Cor. 2.3 |
| `research/lifts/coordinator_check/apsp.c`, `apsp_mt.c` | yes | BFS from **every** vertex of an edge list; checks simple, maximum degree, bipartite, connected and the exact diameter; no symmetry assumed | definition |
| `research/lifts/coordinator_check/apsp_orb.c` | yes | as apsp, but BFS from one vertex per orbit of a level shift that it first verifies to be an automorphism | Lemmas 2.1, 2.5 |
| Lean 4 (`lean/BipartiteDD/Haar/`) | yes | proves `IsBipartiteDegDiam G Δ D` for the specific graph, via Theorem 2.4 and a certificate of words | Thm. 2.4 (formalised) |

The search programs (`haar_gen3.c`, `haar_fast.c`, `haar_sym.c`) also run a full two-source check before writing a
solution. We do not count that check as independent.

**What no checker uses.** None of the checkers uses the orbit symmetry α of §3. The solution files with f = 0 (§3)
even store a translate S·s₀⁻¹ that is not closed under any automorphism of the searched form. It is closed under a map
x ↦ α(x)·c with c ∈ S instead, which is what Lemma 3.1(ii) predicts (c = α(s₀)s₀⁻¹); `orbit_check.py` finds α and c for
every f = 0 record (§5), and for three of them we also found the s₀ for which the stored set times s₀ is α-closed.
So the validity of a record does not depend on any claim in §3: the symmetry was a search device only.

**What remains to be trusted.** The programs, their compilers or interpreters, and the hardware. After this session's
re-checks, every record has been accepted by at least two separately written programs, or by one program and a Lean
proof (§5). Above about 2.4·10⁷ vertices only C programs were run, because the Python checkers need too much memory
there.

---

## 3. Orbit-closed connection sets

### 3.1 Isomorphisms

**Lemma 3.1.** Let a, b ∈ G and ψ ∈ Aut(G). Each of the following maps is an isomorphism.

(i) H(G, S) → H(G, aS): (g, A) ↦ (g, A), (h, B) ↦ (ah, B).

(ii) H(G, S) → H(G, Sb): (g, A) ↦ (b⁻¹g, A), (h, B) ↦ (h, B).

(iii) H(G, S) → H(G, ψ(S)): (g, X) ↦ (ψ(g), X).

(iv) H(G, S) → H(G, S⁻¹): (g, A) ↦ (g, B), (h, B) ↦ (h, A).

Hence H(G, a·ψ(S)·b) and H(G, a·ψ(S)⁻¹·b) are isomorphic to H(G, S).

*Proof.* Each map is a bijection; we check that the edge {(g, A), (sg, B)} of H(G, S) goes to an edge.
(i) Its image is {(g, A), (asg, B)}, an edge of H(G, aS). (ii) Its image is {(b⁻¹g, A), (sg, B)}, and
sg = (sb)(b⁻¹g). (iii) Its image is {(ψ(g), A), (ψ(s)ψ(g), B)}. (iv) Its image is {(g, B), (sg, A)}, and in
H(G, S⁻¹) the vertex (sg, A) is adjacent to (s⁻¹·sg, B) = (g, B). Both graphs have NΔ edges, so the image of the
edge set is the whole edge set. ∎

So one may always assume e ∈ S (replace S by S·s₀⁻¹ for some s₀ ∈ S), which every solution file does.

### 3.2 The construction

**Construction 3.2.** Let α ∈ Aut(G) have order k ≥ 2, and write O(x) = {x, α(x), …, α^(k−1)(x)} and
Fix(α) = {x : α(x) = x}. Choose

- a set F ⊆ Fix(α) with |F| = f (the *fixed generators*), and
- elements x_1, …, x_m whose orbits O(x_j) have size exactly k and are pairwise distinct (hence pairwise disjoint and
  disjoint from F).

Put S = F ∪ O(x_1) ∪ ⋯ ∪ O(x_m). Then α(S) = S and |S| = Δ = f + km. If k is prime, every orbit has size 1 or k, so
x_j ∉ Fix(α) is enough. A search over such S only chooses the f fixed generators and the m orbit representatives.

The automorphisms used for the records in §5 (details per record in the table):

1. **Conjugation times scaling** on G = Q × Z_n: α(x, z) = (gxg⁻¹, rz), with g ∈ Q of order k modulo the centre of Q and
   r ∈ Z_n^× of multiplicative order k. Here Fix(α) = C_Q(g) × {z : (r − 1)z = 0}. If r ≢ 1 modulo every prime factor
   of n (for prime k this is possible exactly when every prime factor of n is ≡ 1 mod k), then r − 1 is a unit mod n and
   the Z_n-part of Fix(α) is {0}; this holds for every record of this type except (7,8), where n = 14 and z ∈ {0, 7} are
   fixed. In SL(2, q) or PSL(2, q), C_Q(g) has order about q (a torus when the characteristic does not divide k). For
   products Q = Q_1 × Q_2, g = (g_1, g_2). This is the k = 3 recipe of most records, and k = 5 for (11,8) and (11,10).
2. **Order 6 with a swap** on SL(2,7)² × Z_31 (the (13,8) record): α(x_1, x_2, z) = (c x_2 c⁻¹, x_1, 6z) with c of order 3.
   Since 6 has order 6 mod 31 and α² is conjugation by (c, c) times z ↦ 36z = 5z, α has order 6.
3. **An involution** on PSL(2,11) × Z_24 (the (6,8) record): conjugation by an involution times z ↦ 11z.

### 3.3 Equivariance

**Proposition 3.3.** Let α ∈ Aut(G) with α(S) = S, and let α̂(g, X) = (α(g), X).

(a) α̂ is an automorphism of H(G, S) that fixes (e, A) and (e, B). Together with the right translations it generates a
group isomorphic to G ⋊ ⟨α⟩ (α̂ ρ_h α̂⁻¹ = ρ_{α(h)}).

(b) For every j ≥ 0 the sets (S⁻¹S)^j, S(S⁻¹S)^j, (SS⁻¹)^j and S⁻¹(SS⁻¹)^j are α-invariant. Hence for each r ≥ 0 the
set U of elements x such that (x, X) is at distance > r from (e, Y) (any fixed X, Y ∈ {A, B}) is a union of ⟨α⟩-orbits.

(c) If k = ord(α) is prime, then |U| ≡ |U ∩ Fix(α)| (mod k).

(d) α permutes the letters of S by some permutation σ. Applying σ letterwise maps reduced A-words (B-words) of length
L bijectively to reduced A-words (B-words) of length L, and (σw)(S) = α(w(S)).

*Proof.* (a) The edge {(g, A), (sg, B)} maps to {(α(g), A), (α(s)α(g), B)}, an edge because α(s) ∈ S; α̂ is a
bijection with inverse (α⁻¹)^. It fixes (e, X) because α(e) = e. And α̂ρ_hα̂⁻¹(g, X) = (α(α⁻¹(g)h), X) =
(gα(h), X). (b) α((S⁻¹S)^j) = (α(S)⁻¹α(S))^j = (S⁻¹S)^j, and similarly for the others; U is the complement of one of
these sets (Proposition 2.2), so it is α-invariant. (c) The ⟨α⟩-orbits in U have size 1 (the points of Fix(α)) or k.
(d) σ is a bijection of S, so it preserves "t_{i+1} ≠ t_i", and α is a homomorphism. ∎

So imposing α(S) = S does not reduce the number of binding words, and it does not make any element more likely to
be covered. What it changes is that coverage events are tied together along orbits: an element is covered exactly
when all of its orbit is.

### 3.4 Involutions in the symmetry group, and why odd order was preferred

For an automorphism β put Anti(β) = {u ∈ G : β(u) = u⁻¹}.

**Proposition 3.4.**

(a) *(Reflection.)* Let β ∈ Aut(G) with β² = id and β(S) = S, inducing σ on S. Let v = (t_1, …, t_{2j}) be a letter
sequence of even length and let v* = (σ(t_{2j}), …, σ(t_1)). Evaluate both with the same sign pattern (both as A-words,
or both as B-words). Then v*(S) = β(v(S))⁻¹. Hence v*(S) = v(S) if and only if v(S) ∈ Anti(β). The sequence v* is
reduced iff v is, and v* = v iff t_{2j+1−i} = σ(t_i) for all i.

(b) *(Uncertainty.)* Let α ∈ Aut(G) have order k and put N_α(u) = u·α(u)⋯α^(k−1)(u). Then
|{u ∈ G : N_α(u) = e}| ≥ |G|/|Fix(α)|. For an involution β this reads |Fix(β)|·|Anti(β)| ≥ |G|.

(c) *(Odd order.)* If α has odd order, then Anti(α) = {u ∈ Fix(α) : u² = e}.

*Proof.* (a) As A-words, v(S) = t_{2j}⁻¹ t_{2j−1} ⋯ t_2⁻¹ t_1, so v(S)⁻¹ = t_1⁻¹ t_2 ⋯ t_{2j−1}⁻¹ t_{2j}, which is the
A-word value of the reversed sequence (t_{2j}, …, t_1). Applying β letterwise gives β(v(S)⁻¹) = v*(S). The B-word case
is the same computation with all signs flipped. The other claims are immediate (σ is a bijection, so
σ(t_{i+1}) ≠ σ(t_i) iff t_{i+1} ≠ t_i).

(b) Let L(x) = x⁻¹α(x). The product N_α(L(x)) telescopes to x⁻¹α^k(x) = e. And L(x) = L(y) iff
yx⁻¹ = α(y)α(x)⁻¹ = α(yx⁻¹), i.e. iff y ∈ Fix(α)x. So the fibres of L are the cosets Fix(α)x, and L has
|G|/|Fix(α)| distinct values, all with N_α = e. For k = 2, N_β(u) = e iff β(u) = u⁻¹.

(c) If α(u) = u⁻¹ then α²(u) = α(u)⁻¹ = u. Since k is odd, α = (α²)^((k+1)/2), so α(u) = u, and then u = u⁻¹. The
converse is clear. ∎

*What this means for the search.* If ⟨α⟩ contains an involution β, then by (a) any binding word containing an
even block v with v(S) ∈ Anti(β) and v* ≠ v takes the same value as the word with v replaced by v*: two distinct words,
one value. By (b), Anti(β) has at least |G|/|Fix(β)| elements; for conjugation in SL(2, q) × Z_n that is a fraction
about 1/q of the group. By (c), a symmetry group of odd order contains no involution, and even the elementwise
condition α(u) = u⁻¹ is confined to involutions inside Fix(α). Odd k still has exact coincidences from (b), but they
equate blocks of different lengths (for k = 3, a block of 2 letters with a block of 4), which cost far fewer words.
How many words each mechanism costs in practice is **heuristic** (research/theory/BEYOND_RANDOM.md §1.4, §4.2).

Two records show that "prefer odd k" is a heuristic preference, not a theorem. At (6,8) an involution won, and at
(13,8) an automorphism of order 6 won (research/theorems/ORDER2.md on branch `claude/thm-order2-symmetry-wejgw7`).
There, the coincidences of (a) occur on a few short cycles of the graph that a solution can avoid, rather than as a
fixed fraction of all words (ORDER2.md §2.1, §3.1).

### 3.5 Why orbit-closed sets help the search (heuristic)

Everything in this subsection is a model or a measurement. None of it is used in §2, §4 or §5.

*Model.* Treat the W binding words as W independent uniform elements of G. The expected number of uncovered elements
is then μ = N e^(−W/N), and a random S is valid with probability about e^(−μ). For α-closed S with α of prime order k,
the uncovered set is a union of orbits (Proposition 3.3), and the model gives P(valid) ≈ e^(−μ_A) with

$$\mu_A \approx \frac{\mu}{k} + \sum_{x\in \mathrm{Fix}(\alpha)\setminus\{e\}} e^{-\lambda/k},\qquad \lambda = W/N,$$

because a free orbit is missed with probability e^(−λ) but there are only about N/k of them, while the words hitting a
fixed point come in groups of k (BEYOND_RANDOM.md §1.2, which also gives the corrections at odd D). So the search
needs about μ/k "independent chances to fail" instead of μ.

*Measurement.* On identical groups, seeds and wall-clock budgets (research/structured/STRUCTURE.md §3, log
`research/structured/runs/cmp1.txt`):

| cell | group | N | μ | random S: solved / runs | orbit-closed, k = 3: solved / runs |
|---|---|---|---|---|---|
| (7,8) | PSL(2,19) × Z_13 | 44,460 | 23.3 | 1/4 | 4/4 (737 to 3,620 evaluations) |
| (7,8) | PSL(2,17) × Z_19 | 46,512 | 34.0 | 0/4 (best cost 6 after 1.2–1.6·10⁶ evaluations) | 4/4 (1.7–5.8·10⁴) |
| (7,8) | PSL(2,19) × Z_14 | 47,880 | 43.0 | 0/4 (best 9–10) | 1/4 (2.3·10⁵) |

Over 32 solved orbit runs, the number of evaluations fits the random-S effort law of research/frontier/SIZE_LAW.md
§4.1 with μ_A in place of μ (BEYOND_RANDOM.md §2).

*What does not change.* The number of α-closed sets is about (N/k)^m |Fix(α)|^(f−1)/m!, against about N^(Δ−1) for all
sets containing e. Setting the expected number of valid sets to 1 gives the same "first-moment ceiling",
μ ≈ (Δ − f) ln N, in both cases (STRUCTURE.md §1). So in this model orbit-closure makes larger groups *searchable*; it
does not make larger valid sets *exist*. Cells whose table value lies above that ceiling (for example (12,8), (14,8),
(16,8)) were not reached, consistent with the model (STRUCTURE.md §6).

---

## 4. Counting bounds and family statements

### 4.1 The per-side Moore bound

**Theorem 4.1.** If |S| = Δ ≥ 2 and diam H(G, S) ≤ D, then |G| ≤ W(Δ, D) = Σ_{j=0}^{D−1} (Δ − 1)^j.

*Proof.* A shortest path never backtracks, so by Proposition 2.2 every element at distance L from (e, A) is the value of
a reduced A-word of length L, and there are at most Δ(Δ − 1)^(L−1) of them for L ≥ 1.
If D = 2k, Theorem 2.4(a) puts every x ∈ G at odd distance ≤ 2k − 1 from (e, A), so

$$|G| \le \sum_{i=0}^{k-1}\Delta(\Delta-1)^{2i} = \sum_{i=0}^{k-1}\big[(\Delta-1)^{2i}+(\Delta-1)^{2i+1}\big] = \sum_{j=0}^{2k-1}(\Delta-1)^j .$$

If D = 2k + 1, Theorem 2.4(b) puts every (x, A) at even distance ≤ 2k from (e, A), so

$$|G| \le 1+\sum_{i=1}^{k}\Delta(\Delta-1)^{2i-1} = 1+\sum_{i=1}^{k}\big[(\Delta-1)^{2i-1}+(\Delta-1)^{2i}\big] = \sum_{j=0}^{2k}(\Delta-1)^j . \qquad ∎$$

Theorem 4.1 is exactly the bipartite Moore bound 2|G| ≤ M^b(Δ, D); we include it because the same count, the number
W(Δ, D) of binding words, is the quantity behind every estimate in §3.5. It uses only one of the two conditions at odd D.

**Corollary 4.2 (cited).** For Δ ≥ 3 and D ∈ {8, 9, 10}, the inequality in Theorem 4.1 is strict.

*Proof.* Equality means 2|G| = M^b(Δ, D), i.e. H(G, S) is a bipartite Moore graph: Δ-regular of diameter D and girth
2D. Such a graph is the incidence graph of a generalized D-gon of order (Δ − 1, Δ − 1). By the Feit–Higman theorem
(J. Algebra 1 (1964) 114–131) thick generalized n-gons exist only for n ∈ {2, 3, 4, 6, 8}, and a generalized octagon of
order (s, t) needs 2st to be a perfect square, which fails for s = t. *Cited, not reproved here.* ∎

For scale: the Haar records in §5 have between 5.1 % ((16,10)) and 22 % ((5,8)) of the Moore bound (§5).

### 4.2 The abelianization bound

For Δ ≥ 1 and D ≥ 2 let ε = 1 if D is even and ε = 0 if D is odd, and

$$A(\Delta,D) = \#\Big\{c\in\mathbb Z^{\Delta} : \textstyle\sum_i c_i=\varepsilon,\ \sum_i |c_i|\le D-1\Big\}.$$

**Theorem 4.3.** Let G′ be the commutator subgroup of G. If |S| = Δ and diam H(G, S) ≤ D, then
|G/G′| ≤ A(Δ, D), and hence |G| ≤ |G′|·A(Δ, D).

*Proof.* Write G/G′ additively and let π : G → G/G′ be the quotient map. For an A-word with letters t_1, …, t_L,
π(w(S)) = Σ_{s ∈ S} c_s π(s), where c_s is the number of positive occurrences of s minus the number of negative ones.
Since the signs alternate starting with +, Σ_s c_s = 1 for L odd and 0 for L even, and Σ_s |c_s| ≤ L. By Theorem 2.4
(remark 1), every x ∈ G is the value of an A-word of length L ≤ D − 1 with L ≡ D − 1 (mod 2), so Σ_s c_s = ε.
Hence π maps onto G/G′ from a set of values indexed by at most A(Δ, D) vectors c. ∎

A(Δ, D) is a polynomial in D of degree Δ − 1 for fixed Δ, while W(Δ, D) is exponential in D. Values (computed by a
short dynamic program, `research/theorems/haar_d8_10/abound.py`):

| Δ | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| A(Δ, 8) | 48 | 216 | 780 | 2,376 | 6,328 | 15,128 | 33,111 | 67,360 | 128,876 | 234,048 | 406,458 | 679,056 | 1,096,740 | 1,719,376 |
| A(Δ, 9) | 61 | 309 | 1,251 | 4,251 | 12,559 | 33,111 | 79,459 | 176,251 | 365,751 | 716,959 | 1,337,961 | 2,392,209 | 4,119,501 | 6,862,501 |
| A(Δ, 10) | 75 | 420 | 1,875 | 7,002 | 22,645 | 65,080 | 169,515 | 406,390 | 907,753 | 1,907,940 | 3,803,865 | 7,241,430 | 13,235,895 | 23,335,504 |

**Corollary 4.4.** Under the hypotheses of Theorem 4.3:

(i) if G is abelian, |G| ≤ A(Δ, D);

(ii) if G = Q × Z_n with Q perfect (Q = Q′), then n ≤ A(Δ, D). This applies to Q = SL(2, q) and PSL(2, q) with
q ≥ 4, and to direct products of such groups;

(iii) if G = Z_m ⋊_r Z_k, then G′ = (r − 1)Z_m × {0} and k·gcd(m, r − 1) ≤ A(Δ, D).

*Proof.* (i) G′ = 1. (ii) G′ = Q′ × {0} = Q × {0}, so G/G′ ≅ Z_n. SL(2, q) is perfect for q ≥ 4 and PSL(2, q) is simple
for q ≥ 4 (standard); a direct product of perfect groups is perfect. (iii) Conjugating (a, 0) by (0, 1) gives (ra, 0),
so G′ contains the commutators ((r − 1)a, 0), i.e. (r − 1)Z_m × {0}. That subgroup is normal (it is stable under
multiplication by r), and the quotient is Z_g × Z_k with g = gcd(m, r − 1) and trivial action (r ≡ 1 mod g), which is
abelian. So G′ = (r − 1)Z_m × {0} and |G/G′| = gk. ∎

For example, the (8,8) record PSL(2,17) × Z_49 has n = 49 ≤ A(8,8) = 15,128, and the metacyclic records have
|G/G′| = 80, 70, 64, 24 at (5,8), (5,9), (4,10), (5,10), against A = 780, 1,251, 420, 1,875. The point of the
corollary is the converse direction: at small Δ an abelian group, or a group with a large abelian quotient, cannot
reach record size. For instance an abelian Haar graph of degree 8 and diameter 8 has at most 2·15,128 = 30,256
vertices, against the table's 201,480. This is why every record uses a group with a large perfect part or a large
commutator subgroup.

### 4.3 Odd diameter: inverse pairs

**Proposition 4.5.** Let i ≥ 1. Reversal (t_1, …, t_{2i}) ↦ (t_{2i}, …, t_1) is a fixed-point-free involution on the
reduced A-words of length 2i, and it inverts values. Hence for every x ∈ G the number of reduced A-words of length 2i
with value x equals the number with value x⁻¹, and for an involution x (x² = e ≠ x) that number is even. The same holds
for B-words.

*Proof.* The value inverts by the computation in Proposition 3.4(a) (with σ = id). Reversal keeps a word reduced. A
reduced word of even length 2i is never its own reversal, since that would force t_i = t_{i+1}. If x = x⁻¹, reversal
permutes the words with value x without fixed points. ∎

At odd D the binding words have even length (Theorem 2.4(b)), so an involution receives its words in pairs.
**Heuristically** it is then missed with probability about e^(−λ/2) instead of e^(−λ), which is why PSL(2, q) alone
(about q²/2 involutions) is a poor choice at odd D and SL(2, q) (one involution, −I) a good one
(research/theory/THRESHOLD.md §3, Corollary 5.2 for a proved version in the regime D fixed, Δ → ∞). Every odd-D record
in §5 uses SL(2, q), a product containing SL(2, q), a PSL(2, q) with a cyclic factor of odd order, or a metacyclic group.

### 4.4 What we cannot prove

- **No infinite family at fixed D.** We have no theorem that produces, for D ∈ {8, 9, 10}, an infinite family of Haar
  graphs (or any graphs) above the table. Each record in §5 is a single graph.
- **The size law is not a theorem.** The observed orders follow N ≈ Δ(Δ − 1)^(D−2) g_Δ / ln(N/μ\*) with a slowly varying
  μ\* (SIZE_LAW.md; g_Δ = (Δ−1)²/((Δ−1)² − 1)). That is a heuristic fitted to data.
- **Random-S theorems are in another regime.** research/theory/THRESHOLD.md proves, for every finite group and fixed D
  as Δ → ∞, that a random S of size Δ gives diameter ≤ D with high probability once the number of distinct-letter words
  exceeds (D−1)!·N ln N, and fails below N(ln N − ln ln N − ω(1)). Those proofs use Suen's inequality (in the form stated
  by Yadin) and are not reproduced here. They say nothing about fixed Δ ≤ 16, the regime of the records.

---

## 5. Records at D = 8, 9, 10

**Status.** Every entry below is a **computer-checked record, not a theorem**: one explicit graph, checked by programs.
Where the Lean column has ✓, the same graph (same group and generators, compared against the file) is also proved in
Lean 4, so for that graph the statement "bipartite, maximum degree ≤ Δ, diameter ≤ D, this many vertices" is a
kernel-checked theorem. "Gain" is measured against the 2013 table (§1.1). The order is also given as a fraction of the
bipartite Moore bound.

### 5.1 The records

<!-- TABLE (generated by research/theorems/haar_d8_10/make_table.py from the logs in haar_d8_10/recheck/) -->
| cell | 2013 table | ours | gain | of Moore bound | group G | orbit structure of S (verified) | Lean | checks before today | this session |
|---|---:|---:|---:|---:|---|---|:---:|---|---|
| (3,8) | 256 | **288** | +12.5 % | 56.5 % | lift of a 4-vertex base over Z_3² ⋊ Z_8 (note 1) | – | ✓ | A | A |
| (5,8) | 9,234 | **9,760** | +5.7 % | 22.3 % | Z_61 ⋊_8 Z_80 | – | (9,576) | B | B, A |
| (6,8) | 29,790 | **31,680** | +6.3 % | 16.2 % | PSL(2,11) × Z_24 | k = 2, f = 0: 2+2+2 | (30,576) | B | B, I, F, A |
| (7,8) | 80,940 | **95,760** | +18.3 % | 14.3 % | PSL(2,19) × Z_14 | k = 3: 1+3+3 | ✓ | B ×2 | B, I, F, A |
| (8,8) | 201,480 | **239,904** | +19.1 % | 12.5 % | PSL(2,17) × Z_49 | k = 3: 1+1+3+3 | ✓ | B ×2 | B, I, F |
| (9,8) | 449,480 | **540,360** | +20.2 % | 11.3 % | PSL(2,19) × Z_79 | k = 3, f = 0: 3+3+3 | ✓ | B ×2 | B, I, F |
| (11,8) | 2,246,940 | **2,258,520** | +0.5 % | 10.2 % | PSL(2,59) × Z_11 | k = 5: 1+5+5 | – | B, I, P, G | B, F |
| (13,8) | 5,314,680 | **6,999,552** | +31.7 % | 9.0 % | SL(2,7)² × Z_31 | k = 6 (swap): 1+6+6 | – | B, G (+3 on a branch) | B, I |
| (15,8) | 14,172,480 | **18,128,880** | +27.9 % | 8.0 % | SL(2,109) × Z_7 | k = 3, f = 0: 3+3+3+3+3 | – | B, C, G | B, I, F |
| (5,9) | 27,936 | **29,540** | +5.7 % | 16.9 % | Z_422 ⋊_5 Z_35 | – | (28,560) | B | B, A |
| (6,9) | 117,360 | **127,296** | +8.5 % | 13.0 % | SL(2,17) × Z_13 | k = 3, f = 0: 3+3 | ✓ | B ×2 | B, I, F, A |
| (7,9) | 400,160 | **462,840** | +15.7 % | 11.5 % | PSL(2,29) × Z_19 | k = 3: 1+3+3 | ✓ | B ×3 | B, I, F |
| (8,9) | 1,091,232 | **1,341,600** | +22.9 % | 10.0 % | SL(2,25) × Z_43 | k = 3: 1+1+3+3 | – | B | B, I |
| (9,9) | 2,961,536 | **3,499,776** | +18.2 % | 9.1 % | PSL(2,7) × SL(2,7) × Z_31 | k = 3, f = 0: 3+3+3 | – | B ×2, G | B, I |
| (10,9) | 7,057,400 | **8,003,856** | +13.4 % | 8.3 % | SL(2,83) × Z_7 | k = 3: 1+3+3+3 | – | B, I, C, C2, G | B, F |
| (11,9) | 15,200,448 | **16,792,080** | +10.5 % | 7.6 % | SL(2,61) × Z_37 | k = 3: 1+1+3+3+3 | – | B, I, C, C2, G | B |
| (12,9) | 30,001,152 | **34,026,720** | +13.4 % | 7.2 % | SL(2,41) × Z_247 | k = 3, f = 0: 3+3+3+3 | – | C, C2, G | C |
| (13,9) | 50,990,610 | **67,742,688** | +32.9 % | 7.2 % | SL(2,103) × Z_31 | k = 3: 1+3+3+3+3 | – | C, G | C, C2 |
| (14,9) | 95,087,738 | **116,068,656** | +22.1 % | 6.6 % | SL(2,67) × Z_193 | k = 3: 1+1+3+3+3+3 | – | C, C2, G | C |
| (15,9) | 168,016,334 | **208,029,120** | +23.8 % | 6.5 % | SL(2,79) × Z_211 | k = 3, f = 0: 3+3+3+3+3 | – | C, C2, G | C |
| (16,9) | 288,939,118 | **337,394,400** | +16.8 % | 6.1 % | SL(2,151) × Z_49 | k = 3: 1+3+3+3+3+3 | – | C, C2, G (note 3) | – |
| (4,10) | 11,748 | **12,416** | +5.7 % | 21.0 % | Z_97 ⋊_19 Z_64 | – | ✓ | A | A |
| (5,10) | 90,068 | **95,472** | +6.0 % | 13.7 % | Z_1989 ⋊_461 Z_24 | – | ✓ | A | A |
| (6,10) | 452,032 | **524,160** | +16.0 % | 10.7 % | SL(2,5) × PSL(2,7) × Z_13 | k = 3, f = 0: 3+3 | ✓ | B ×2 | B, I |
| (7,10) | 1,987,380 | **2,237,760** | +12.6 % | 9.3 % | PSL(2,5) × SL(2,8) × Z_37 | k = 3: 1+3+3 | – | B, G | B, I |
| (8,10) | 6,927,210 | **7,818,096** | +12.9 % | 8.3 % | SL(2,67) × Z_13 | k = 3: 1+1+3+3 | – | C, G | B, I, C2, F |
| (9,10) | 20,017,260 | **23,975,280** | +19.8 % | 7.8 % | PSL(2,71) × Z_67 | k = 3, f = 0: 3+3+3 | – | P ×2, G | I, P |
| (10,10) | 50,331,156 | **60,141,120** | +19.5 % | 6.9 % | SL(2,79) × Z_61 | k = 3: 1+3+3+3 | – | C, C2, G | C |
| (11,10) | 130,592,354 | **148,729,680** | +13.9 % | 6.7 % | PSL(2,89) × Z_211 | k = 5: 1+5+5 | – | P, G | P |
| (12,10) | 300,383,050 | **325,832,976** | +8.5 % | 6.3 % | SL(2,107) × Z_133 | k = 3, f = 0: 3+3+3+3 | – | C, C2, G | C |
| (13,10) | 617,330,936 | **677,714,400** | +9.8 % | 6.0 % | SL(2,199) × Z_43 | k = 3: 1+3+3+3+3 | – | C, C2, G | – |
| (14,10) | 1,213,477,190 | **1,326,627,120** | +9.3 % | 5.8 % | SL(2,139) × Z_247 | k = 3: 1+1+3+3+3+3 | – | C, C2, G | – |
| (15,10) | 2,300,326,510 | **2,467,618,800** | +7.3 % | 5.5 % | SL(2,149) × Z_373 | k = 3, f = 0: 3+3+3+3+3 | – | C, G | – |
| (16,10) | 4,119,507,330 | **4,220,872,800** | +2.5 % | 5.1 % | SL(2,151) × Z_613 | k = 3: 1+3+3+3+3+3 | – | C, G | – |
<!-- /TABLE -->

*Solution files.* `research/frontier/sols/<cell>_…txt`, one per cell; the stems are listed in `make_table.py`. Exceptions:
(3,8), (4,10) and (5,10) are in `research/lifts/sols/`.

*Orbit structure.* "k = 3: 1+3+3" means that S is closed under an automorphism α of order k of the form in
Construction 3.2, and α splits S into cycles of the sizes shown (1 = a fixed generator). "f = 0" means no fixed
generator; such files store a translate (§2.6), which is closed under x ↦ α(x)c instead. Each entry was verified from
the file alone by `orbit_check.py` (single-factor groups over prime fields) or `orbit_check2.py` (products, GF(25), and
the order-6 swap of (13,8)); outputs in `recheck/orbit_check.log` and `recheck/orbit_check2.log`. "–" means the graph
was not found by an orbit search and no symmetry is claimed.

*Checker letters.* B = `build_haar2.py`; I = `check_haar_indep.py`; C = `haarcheck_sl.c`; C2 = `haarcheck2.c`;
P = `haarcheck_psl.c`; F = `research/theorems/haar_d8_10/hc_factor.c` (written for this note, see §5.3);
A = all-pairs BFS with `apsp.c` or `apsp_mt.c`, on an edge list built by `research/lifts/coordinator_check/build.py`
(its own group code) or by `build_haar2.py`, and failing as it should with D − 1; G = `bigcheck_indep.c` (cloud runs;
its source is not in the repository, §5.2). Each letter is a separately written program (C and C2 are two different C
programs). "B ×2" means the same program was run twice (by the search session and at harvest, with the same edge-list
sha256).

*Lean.* ✓ = a theorem `nb_Δ_D_…` in `lean/BipartiteDD/Haar/<dir>/Record*.lean` for this graph, with its own
`Axioms.out.txt` listing only `propext`, `Classical.choice`, `Quot.sound` (no `sorry`, no `native_decide`). A number in
brackets is the largest earlier (smaller) graph of the cell proved in Lean. These modules are not imported by the default
target `lean/BipartiteDD.lean`; build each with `lake build BipartiteDD.Haar.<dir>.<file>` (for example
`lake build BipartiteDD.Haar.D7D8b.Record`).

**Notes.**

1. (3,8) is the only record here that is not a Haar graph: a 72-fold regular cover of a cubic bipartite multigraph on
   2 + 2 vertices (edges 0–2 twice, 0–3, 1–2, 1–3 twice), with voltages in Z_3² ⋊_M Z_8, M = [[0, 2], [1, 0]]
   (`research/lifts/sols/c1r_d3D8_n288_b2_3_0_aff302108_s1.txt`). For a cell this well studied, 288 against 256 is a
   large jump; the table audit found no source for 256 and no later value (AUDIT.md §3, §8).
2. (11,10): the table value is 130,592,354 (§6.1), not 0 as the repository README says.
3. (16,9): the earlier cloud report `research/frontier/runs/cloudcheck/d16D9_sl_151_49_orb3_s1.txt` has a header copied
   from the (14,10) report (file name and sha256), while its checker output is for the (16,9) graph. The search session's
   own C and C2 runs (`research/structured/runs/d16D9_sl_151_49_orb3_s1.log`) and this session's runs are for the right
   file.
4. The table values at (11,8) and (15,8) are among the D = 8 values from Gómez's ΩH_q that the table audit could not
   reproduce at diameter 8 (§6.1), and (15,8) repeats the (14,8) value. Our graphs are checked either way; only the size
   of the gain is in question there.

### 5.2 Gaps in the earlier record-keeping, and what this session did about them

An audit of the logs (2026-10-25) found the following. None of them affects whether a graph is valid; they affect how
well the evidence was recorded.

- **Single-program cells.** Before today, (5,8), (5,9), (6,8) and (8,9) had only one checker run each (build_haar2 at
  harvest), and (13,9), (7,10), (8,10), (11,10), (15,10), (16,10) had only one recorded run (a cloud job with two
  checkers, whose output the harvest log copies). This session re-ran every graph (column "this session"). After it,
  every cell has been accepted by at least two separately written programs, or by one program and a Lean proof.
- **`bigcheck_indep.c` is not in the repository**, nor its validation output, although it was the second checker for
  every graph above 2·10⁷ vertices. Its report notes that it shares the file conventions with the other checkers, so a
  shared misreading of the file format would not be caught. This is why `hc_factor.c` was written (§5.3).
- **The harvest tool** (`labctl`) is not in the repository; its checks are only described in SIZE_LAW.md and old commit
  messages.
- **`check_haar_indep.py`** had been run on only three current records ((10,9), (11,9), (11,8)); this session ran it on
  the other 14 Haar records up to 2.4·10⁷ vertices that it can read (it does not read metacyclic groups).
- **Labels.** The README "Method" column calls (13,8), (7,10), (8,10), (11,10), (15,10) and (16,10) "finite geometry";
  all six are orbit-search Haar graphs (verified above). It calls (8,9) "evolutionary search"; the file is an orbit-closed
  Haar graph of SL(2,25) × Z_43. (5,8) and (5,9) are metacyclic Haar graphs; no log in the repository shows how they were
  found.

### 5.3 The checker written for this note

`research/theorems/haar_d8_10/hc_factor.c` handles G = Q × Z_n with Q = SL(2, p) or PSL(2, p), p prime. It enumerates Q by
brute force over all (a, b, c, d) ∈ [0, p)⁴ with ad − bc = 1 (for PSL keeping the lexicographically smaller of ±X),
checks |Q| against the formula, turns each generator (M, t) into two permutation tables of Q (X ↦ MX and X ↦ M⁻¹X),
checks that both are bijections, and runs the two searches of Corollary 2.3 on Q × Z_n with bitsets. It reads only the
`mat(…)` and `z=` fields of the file. It reports VALID on the records, and INVALID on a file with one generator altered
and on the (7,8) file with D lowered to 7 (`recheck/hc_factor_negative.log`).

### 5.4 Cells at D = 8, 9, 10 that we do not beat

| cell | 2013 table | holder (wiki colour) | remark |
|---|---:|---|---|
| (4,8) | 2,184 | Loz | a Haar graph of Z_91 ⋊ Z_12 of exactly this order exists (table audit) |
| (10,8) | 1,176,480 | Delorme–Gómez–Quisquater | value from Gómez's ΩH_7; did not check out at diameter 8 as read (§6.1) |
| (12,8) | 4,650,100 | Delorme–Gómez–Quisquater | the same |
| (14,8) | 14,172,480 | Delorme–Gómez–Quisquater | the same |
| (16,8) | 36,201,060 | Delorme–Gómez–Quisquater | the same |
| (3,9) | 506 | Loz | a Haar graph of Z_23 ⋊ Z_11 of exactly this order exists (table audit) |
| (4,9) | 4,970 | Loz | a Haar graph of Z_71 ⋊ Z_35 of exactly this order exists (table audit) |
| (3,10) | 800 | Delorme–Gómez–Quisquater | no source; a lift of exactly this order was found by the table audit |

The heuristic of §3.5 places (12,8), (14,8) and (16,8) above the first-moment ceiling for random-like and
orbit-closed S (STRUCTURE.md §6). If the table values there are right, they come from structure that our searches do
not reproduce.

---

## 6. Prior art, and what is ours

Tags: **[read]** the lab read the primary source; **[secondary]** known from a survey, an abstract or a citation only;
**[inferred]** deduced from table values, not stated anywhere. The literature notes behind this section are
`research/theory/LITERATURE.md` and `research/projects/table-audit/lit/LITERATURE.md` (branch `claude/table-audit-1odopy`).

### 6.1 Prior art

**Who holds the table at D = 8, 9, 10.** From the wiki's colour key, parsed on 2026-10-25 [read]:

- Most cells are E. Loz's. The survey says Loz, Pérez-Rosés and Pineda-Villavicencio "adapted the voltage-assignment-based
  method developed by Loz and Širáň for general graphs to the case of bipartite graphs; this resulted in updating more
  than one third of the table" [read, survey]. Loz–Širáň (Australas. J. Combin. 41 (2008) 63–80) lift small base graphs
  with voltages in metacyclic groups Z_m ⋊ Z_n found by random search [read]. The bipartite paper (a 2012 preprint) and
  Loz's thesis (Auckland 2009, restricted access) could not be read, and no graphs survive where we could reach them
  [secondary]. Many of these table orders factor as 2·p·k with k | p − 1, the order of a Haar graph of Z_p ⋊ Z_k, so
  these are probably dipole lifts, i.e. Haar graphs of metacyclic groups [inferred]. The lab's table audit found Haar
  graphs of metacyclic groups at exactly 23 of the Loz orders, 17 of them at D = 8–10: (3,9), (4,8), (4,9), (4,10),
  (5,8)–(5,10), (6,8)–(6,10), (7,8)–(7,10), (8,8), (8,9), (9,8), (9,9) [computer-checked; AUDIT.md §3]. That shows such graphs exist
  at those orders, not that they are Loz's.
- D = 8 with Δ = 10, 11, 12, 14, 15, 16: J. Gómez Martí's thesis (UPC Barcelona, 1986, §2.9.3) lists exactly these values
  as orders of a compound ΩH_q of generalized hexagons [read]; the wiki credits Delorme–Gómez–Quisquater, "On large
  bipartite graphs", which was never published [secondary]. The lab's rebuild of ΩH_q as read from the thesis has the
  right order but diameter 9 (AUDIT.md §4). This may be a misreading of the thesis's figure, so we do not claim the
  values are wrong. (15,8) reuses the (14,8) value.
- (13,8) = 5,314,680 = 15·|H(11)| has no traced construction (D8_NUMEROLOGY.md on branch
  `claude/d8-table-numerology-mi6but` studies these numbers; it proves bounds for natural lift families but does not
  find the construction).
- **(11,10).** The survey PDF prints "130 592 1354"; every wiki revision has 130,592,354 (AUDIT.md §1). The repo README
  lists the table value as 0. The correct comparison is 130,592,354; our 148,729,680 is 13.9 % above it.
- **After 2013.** The wiki changed only at (13,3) and (15,3) (Araujo-Pardo–López). A literature search found no later
  paper with a larger bipartite graph at D = 8–10 (AUDIT.md lit §8). The search was not exhaustive.

**Haar graphs and lifts.** Haar graphs: M. Hladnik, D. Marušič, T. Pisanski, *Cyclic Haar graphs*, Discrete Math. 244
(2002) [secondary]; A. Estélyi, T. Pisanski, *Which Haar graphs are Cayley graphs?*, Electron. J. Combin. 23(3) (2016)
[read: abstract]. A Haar graph is a regular cover of a dipole (standard voltage-graph theory). In the bipartite
degree–diameter problem, Haar graphs of cyclic groups appear at D = 3 (Feria-Purón–Miller–Pineda-Villavicencio,
Discrete Math. 313 (2013), the graphs Φ_m) [read], and dipole lifts over metacyclic groups are probably behind Loz's
values [inferred].

**Matrix groups.** Cayley graphs of SL(2, p) with random generators are expanders (Bourgain–Gamburd, Ann. of Math. 167
(2008)) and every generating set gives diameter O((log p)^c) (Helfgott, same volume) [read]. These results do not
give the constant 1 in diam ≈ log_{Δ−1} |G| that the records need.

**Symmetric connection sets.** Requiring a connection set to be invariant under a group automorphism is an old device.
The Singer difference sets behind the D = 3 Moore graphs are fixed, up to translation, by the multiplier z ↦ qz of
order 3 (Hall's multiplier theorem) [classical]. We do not claim the idea is new.

**Elementary statements.** We claim no novelty for Lemma 1.2, Lemma 2.1, Theorem 2.4, Lemma 3.1 or Theorem 4.1; they
are routine and we include them so that the checks can be audited. Loz's thesis abstract says it "generalizes the
upper bound for abelian lifts of dipoles" [secondary], so a bound of the type of Theorem 4.3 is probably known in some
form; ours is stated for every group through G/G′. We have not seen Propositions 3.4 and 4.5 stated, but they are short
and may be folklore.

### 6.2 What is ours

1. **The graphs of §5.** 34 cells at D = 8, 9, 10 where our graph is larger than the table. All are Haar graphs except
   (3,8), which is a voltage lift. Most are Haar graphs of SL(2, q), PSL(2, q) or a product of two such groups, times a
   cyclic group, with 3·10⁴ to 4.2·10⁹ vertices. We have not found earlier use of SL(2, q)-type groups for bipartite
   records at D ≥ 8. Because Loz's constructions are unavailable, we cannot rule out that the small metacyclic cells
   ((5,8), (5,9), (4,10), (5,10)) use a method close to his.
2. **The search.** Simulated annealing over S with a bitset BFS evaluator (`research/frontier/haar_gen3.c`,
   `research/structured/haar_fast.c`), and orbit-closed S (Construction 3.2, `research/structured/haar_sym.c`) as a search
   device, with the measured effect of §3.5.
3. **The checks.** Independent checkers (§2.6), and Lean proofs for the graphs that are small enough (§5).
4. **The theory notes** (`research/frontier/SIZE_LAW.md`, `research/theory/THRESHOLD.md`, `BEYOND_RANDOM.md`, and
   `ORDER2.md`): a fitted size law, heuristics for choosing groups and symmetries, and some theorems in the regime D
   fixed, Δ → ∞. They are not claims of this note.

---

## 7. How to re-check

Everything below runs on a laptop except the largest low-memory checks (about 1.6 GB of memory and 1–2 hours for
(16,10) on one core).

```bash
# a Haar record: independent rebuild of the group and the graph, BFS from (e,A) and (e,B)  (Corollary 2.3)
python3 research/frontier/build_haar2.py research/frontier/sols/d7D8_psl_19_14_orb3_s1.txt

# the same with the independent Python checker
python3 research/frontier/check_haar_indep.py research/frontier/sols/d7D8_psl_19_14_orb3_s1.txt

# low-memory checkers for SL(2,p) x Z_n and PSL(2,p) x Z_n (p prime), any size
cc -O3 -o hcsl research/frontier/haarcheck_sl.c
./hcsl research/frontier/sols/d16D10_sl_151_613_orb3_s1.txt
cc -O3 -o hcpsl research/structured/tools/haarcheck_psl.c
./hcpsl research/frontier/sols/d11D10_psl_89_211_orb5_ORBW5_s11.txt

# the checker written for this note (SL(2,p) or PSL(2,p) times Z_n, p prime)
cc -O3 -o hc_factor research/theorems/haar_d8_10/hc_factor.c
./hc_factor research/frontier/sols/d11D10_psl_89_211_orb5_ORBW5_s11.txt

# all-pairs BFS that assumes no symmetry (write the edge list first)
python3 research/frontier/build_haar2.py research/frontier/sols/d7D8_psl_19_14_orb3_s1.txt /tmp/edges.txt
cc -O2 -o apsp research/lifts/coordinator_check/apsp.c && ./apsp /tmp/edges.txt 7 8

# the orbit structure of S (Construction 3.2): finds alpha and prints the cycle sizes of S
python3 research/theorems/haar_d8_10/orbit_check.py research/frontier/sols/d7D8_psl_19_14_orb3_s1.txt 3

# the numbers A(Delta, D) of Theorem 4.3
python3 research/theorems/haar_d8_10/abound.py

# Lean (needs elan; downloads Mathlib's cache); build one module at a time
cd lean && lake exe cache get && lake build BipartiteDD.Haar.Main
```

The outputs of this session's re-checks are in `research/theorems/haar_d8_10/recheck/`, and
`python3 research/theorems/haar_d8_10/make_table.py` regenerates the table of §5.1 from them.

---

## Appendix A. One record written out: Δ = 7, D = 8, 95,760 vertices

G = PSL(2, 19) × Z_14, of order 3,420 · 14 = 47,880. Matrices are taken modulo ±I. The file
`research/frontier/sols/d7D8_psl_19_14_orb3_s1.txt` lists

| | matrix | z |
|---|---|---|
| s_0 | [[1, 0], [0, 1]] | 0 |
| s_1 | [[2, 13], [14, 6]] | 6 |
| s_2 | [[4, 13], [7, 4]] | 12 |
| s_3 | [[2, 7], [7, 6]] | 10 |
| s_4 | [[6, 2], [8, 6]] | 1 |
| s_5 | [[6, 13], [15, 1]] | 9 |
| s_6 | [[1, 4], [12, 11]] | 11 |

*Symmetry (computer-checked, `orbit_check.py`).* Let g = [[1, 3], [6, 0]] (determinant 1, order 3 in PSL(2, 19)) and
α(x, z) = (gxg⁻¹, 9z). Then 9 has order 3 mod 14, α has order 3, and α permutes S as s_0 ↦ s_0,
s_1 ↦ s_2 ↦ s_3 ↦ s_1 and s_4 ↦ s_5 ↦ s_6 ↦ s_4 (on the z-coordinates: 6 ↦ 12 ↦ 10 ↦ 6 and 1 ↦ 9 ↦ 11 ↦ 1). So S
is Construction 3.2 with k = 3, f = 1, m = 2.

*Diameter (computer-checked).* By Theorem 2.4(a) with D = 8, diam H(G, S) ≤ 8 means that every element of G is a product
s_{i_7} s_{i_6}⁻¹ s_{i_5} s_{i_4}⁻¹ s_{i_3} s_{i_2}⁻¹ s_{i_1} of seven letters with alternating signs. There are
7·6⁶ = 326,592 reduced such words for 47,880 elements. build_haar2.py, check_haar_indep.py and the coordinator's checks
confirm the covering (§5), and the graph is proved in Lean (`lean/BipartiteDD/Haar/`, §5).

The order is 14.25 % of the bipartite Moore bound 671,846; the table value is 80,940.
