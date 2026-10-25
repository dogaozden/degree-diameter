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
6. Prior art, and what this note contributes
7. How to re-check

---

## 0. Summary of statements

| # | statement | label |
|---|---|---|
| Lemma 1.2 | H(G,S) is bipartite, simple, Δ-regular, of order 2\|G\|; right translations act regularly on each side | Lemma |
| Lemma 2.1 | the diameter is the largest eccentricity over one vertex from each orbit of any automorphism group | Lemma |
| Prop. 2.2 | distances from (e,A) and (e,B) are word lengths in S and S⁻¹ | Proposition |
| Cor. 2.3 | diam H(G,S) = max(ecc(e,A), ecc(e,B)) | Corollary |
| Thm. 2.4 | covering criterion: D = 2κ needs S(S⁻¹S)^(κ−1) = G; D = 2κ+1 needs (S⁻¹S)^κ = G and (SS⁻¹)^κ = G | Theorem |
| Lemma 3.1 | H(G,S) ≅ H(G, a·ψ(S)^(±1)·b) for a, b ∈ G, ψ ∈ Aut(G) | Lemma |
| Prop. 3.3 | if α(S) = S, then α acts on H(G,S) fixing (e,A), (e,B); every uncovered set is a union of α-orbits | Proposition |
| Prop. 3.4 | for an involution β: \|Fix(β)\|·\|Anti(β)\| ≥ \|G\|; if moreover β(S) = S, even blocks with value in Anti(β) pair up with equal values; for odd order, Anti(α) is the set of elements of order ≤ 2 in Fix(α) | Proposition |
| §3.5 | why orbit-closed S makes larger groups searchable | Heuristic, measured |
| Thm. 4.1 | \|G\| ≤ Σ_{j<D} (Δ−1)^j (the bipartite Moore bound, per side); strict for D = 8, 9, 10 and Δ ≥ 3 | Theorem (strictness cited) |
| Thm. 4.3 | \|G/G′\| ≤ A(Δ,D) = Θ(D^(Δ−1)) for fixed Δ | Theorem |
| Cor. 4.4 | the same for abelian groups, for Q × Z_n with Q perfect, and for metacyclic groups | Corollary |
| Prop. 4.5 | at odd D, the binding words hitting an involution come in pairs | Proposition |
| Prop. 4.6 | a cyclic lift of a bipartite graph of diameter δ along bijections from points to lines has diameter ≤ δ + 2 if the voltages cover Z_n (not Haar graphs; below the table at D = 8) | Proposition |
| §5 | 34 cells at D = 8, 9, 10 where our graph is larger than the 2013 table | Computer-checked (12 also in Lean, at the record or at an earlier value) |

---

## 1. Setting and notation

### 1.1 The problem

N^b(Δ, D) is the largest order of a bipartite graph with maximum degree at most Δ and diameter at most D. The bipartite
Moore bound is

$$N^b(\Delta,D) \le M^b(\Delta,D) = 2\sum_{j=0}^{D-1}(\Delta-1)^j .$$

"The table" means Table 4 of M. Miller and J. Širáň, *Moore graphs and beyond: a survey of the degree/diameter
problem*, Electron. J. Combin. Dynamic Survey DS14v2 (2013), which the Combinatorics Wiki reproduces. At D = 8, 9, 10
the wiki values equal the survey values, except at (11,10), where the survey PDF has a misprint (§6.1) (checked against
the live wiki page on 2026-10-25, `research/projects/table-audit/AUDIT.md` §1 on branch `claude/table-audit-1odopy`).

### 1.2 Haar graphs

**Definition 1.1.** Let G be a finite group with identity e and order N, and let S ⊆ G with |S| = Δ. The *Haar graph*
H(G, S) has vertex set G × {A, B}, and (g, A) is adjacent to (sg, B) for every g ∈ G and s ∈ S.

*Conventions.* Some authors join (g, A) to (gs, B). The map (g, X) ↦ (g⁻¹, X) is an isomorphism from our H(G, S) to
that graph built with S⁻¹, and H(G, S⁻¹) ≅ H(G, S) by Lemma 3.1(iv), so the two conventions give isomorphic graphs.
H(G, S) is also the regular G-cover (derived graph) of the dipole with Δ parallel edges carrying the voltages s ∈ S,
and, in the language of bi-Cayley graphs, BiCay(G, ∅, ∅, S). For G = Z_n these are the cyclic Haar graphs of Hladnik,
Marušič and Pisanski. All our files and checkers use the left convention of Definition 1.1
(`research/frontier/build_haar2.py`, header; `lean/BipartiteDD/Haar/Graph.lean`, where `inl g ~ inr h` iff
`h * g⁻¹ ∈ S`).

*Geometric reading.* Call the A-vertices points and the B-vertices lines. The line (h, B) is incident with the points
(s⁻¹h, A), s ∈ S, so H(G, S) is the incidence graph of the incidence structure whose blocks are the right translates
S⁻¹h of S⁻¹ (the development of S⁻¹). At D = 3 with |G| = Δ² − Δ + 1, counting shows that S⁻¹S = G holds iff every
non-identity element of G is s⁻¹t for a unique pair (s, t), i.e. S is a planar difference set; then any two points lie
on exactly one block, the structure is a projective plane, any two lines meet, and SS⁻¹ = G follows, so Theorem 2.4(b)
below holds; for example H(Z_7, {0, 1, 3}) is the incidence graph of the Fano plane, and Theorem 4.1 holds with equality
there. We say "order of G" for |G|; the graph has 2|G| vertices.

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

For X, Y ⊆ G write XY = {xy : x ∈ X, y ∈ Y}, X⁻¹ = {x⁻¹ : x ∈ X}, X⁰ = {e} and X^j = X·X^(j−1). If S ≠ ∅ then
e ∈ S⁻¹S, so (S⁻¹S)^i ⊆ (S⁻¹S)^j for i ≤ j, and likewise for SS⁻¹.

An *A-word* of length L is a sequence (t_1, …, t_L) of letters t_i ∈ S. Its *value* w(S) ∈ G is

$$w(S) = \cdots\, t_4^{-1}\, t_3\, t_2^{-1}\, t_1 \qquad(\text{signs } +,-,+,-,\dots \text{ read from the right}).$$

A *B-word* has the opposite signs: w(S) = ⋯ t_3⁻¹ t_2 t_1⁻¹. A word is *reduced* if t_{i+1} ≠ t_i for all i. There are
Δ(Δ−1)^(L−1) reduced words of each kind and length L ≥ 1. Walks in H(G, S) that start at (e, A) correspond exactly to
A-words, and a walk backtracks exactly when its word is not reduced (Proposition 2.2).

Throughout,

$$W(\Delta,D)=\sum_{j=0}^{D-1}(\Delta-1)^j = \tfrac12 M^b(\Delta,D).$$

### 1.4 The groups

- SL(2, q), PSL(2, q) = SL(2, q)/{±I} and PGL(2, q) = GL(2, q)/(scalars), of orders q(q² − 1), q(q² − 1)/gcd(2, q − 1)
  and q(q² − 1). For q = p^e with e > 1 the field is GF(p)[x]/(P), with the irreducible polynomial P named in the
  file (for example `sl 25 poly x^2+2`); a field element c_0 + c_1 x + ⋯ is written as the integer c_0 + c_1 p + ⋯.
- Direct products Q × Z_n and Q_1 × Q_2 × Z_n with Q, Q_i of the types above (file spec `prod Q1 Q2 n <n>`).
- Metacyclic groups Z_m ⋊_r Z_ℓ: pairs (a, j) ∈ Z_m × Z_ℓ with (a, j)(b, i) = (a + r^j b, j + i), where r^ℓ ≡ 1 (mod m).
  The order is mℓ. Only r^ℓ ≡ 1 is required, so the action need not be faithful: for (5,8), r = 8 has order 20 mod 61
  while ℓ = 80, and for (4,10), r = 19 has order 32 mod 97 while ℓ = 64. (We write ℓ here because k is the order of
  the automorphism α in §3.)

*File format* (`research/frontier/sols/*.txt`). The header is `Δ D <group> n <n> N <|G|>`, then Δ lines
`<index> mat(a,b,c,d) z=Z` for the element ([[a, b], [c, d]], Z) of Q × Z_n (`prod[mat(…);mat(…)] z=Z` for products,
`meta(a=…,j=…)` for metacyclic groups, whose header `meta m k r` means Z_m ⋊_r Z_ℓ with ℓ = k; the index is the
search program's own and is ignored by the checkers). The first listed element is e in every file; by Lemma 3.1 this is
no loss of generality.

---

## 2. The covering criterion, and why the symmetric checks are exact

This section is what a referee needs in order to trust the record checks. Every two-source checker in §5 computes the
eccentricities of exactly two vertices, (e, A) and (e, B). Lemma 2.1 and Lemma 1.2(b) say why that gives the
diameter, and Theorem 2.4 says what is being verified in group-theoretic terms.

For a vertex v of a graph X, ecc(v) = max_u d(v, u), with d(v, u) = ∞ if there is no path. diam X = max_v ecc(v).

**Lemma 2.1 (orbit representatives).** Let Γ be a group of automorphisms of a finite graph X, and let R be a set of
vertices that meets every Γ-orbit. Then diam X = max_{r ∈ R} ecc(r).

*Proof.* "≥" is clear. Let u, v be vertices. Choose γ ∈ Γ and r ∈ R with γ(u) = r. Automorphisms preserve distances,
so d(u, v) = d(γu, γv) = d(r, γv) ≤ ecc(r). ∎

**Proposition 2.2 (distances from the two base vertices).** Let S ≠ ∅. For x ∈ G and j ≥ 0:

| this holds | if and only if |
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

(a) If D = 2κ, then diam H(G, S) ≤ D if and only if S(S⁻¹S)^(κ−1) = G.

(b) If D = 2κ + 1, then diam H(G, S) ≤ D if and only if (S⁻¹S)^κ = G and (SS⁻¹)^κ = G.

*Proof.* (a) Suppose diam ≤ 2κ. For x ∈ G, d((e, A), (x, B)) is odd (the graph is bipartite) and at most 2κ, hence at
most 2(κ − 1) + 1, so x ∈ S(S⁻¹S)^(κ−1) by Proposition 2.2. Conversely, suppose S(S⁻¹S)^(κ−1) = G. Then
d((e, A), (x, B)) ≤ 2κ − 1 for every x, and applying ρ_g, d((g, A), (h, B)) = d((e, A), (hg⁻¹, B)) ≤ 2κ − 1 for all
g, h. Fix s ∈ S. For two A-vertices, (g′, A) is adjacent to (sg′, B), so d((g, A), (g′, A)) ≤ d((g, A), (sg′, B)) + 1
≤ 2κ. For two B-vertices, (h′, B) is adjacent to (s⁻¹h′, A), so d((h, B), (h′, B)) ≤ d((s⁻¹h′, A), (h, B)) + 1 ≤ 2κ.

(b) Suppose diam ≤ 2κ + 1. Distances between vertices on the same side are even, hence at most 2κ, so
(S⁻¹S)^κ = G and (SS⁻¹)^κ = G by Proposition 2.2. Conversely, if both hold, then by Proposition 2.2 and ρ_g all
same-side distances are at most 2κ. For (g, A) and (h, B), (g, A) is adjacent to (sg, B), so
d((g, A), (h, B)) ≤ 1 + d((sg, B), (h, B)) ≤ 2κ + 1. ∎

*Remarks.*

1. In terms of reduced words (Proposition 2.2): for D = 2κ every x ∈ G must be the value of a reduced A-word of odd
   length ≤ D − 1; for D = 2κ + 1 every x must be the value of a reduced A-word of even length ≤ D − 1 **and** of a
   reduced B-word of even length ≤ D − 1. These are the "binding words". On each side there are W(Δ, D) of them
   (counting the empty word at odd D; §4.1), so at odd D there are 2W in all.
2. At even D a single search from (e, A) decides the diameter. The checkers run both searches at every D; that is
   more than needed and is exact by Corollary 2.3.
3. At odd D the second condition is the first one for S⁻¹. If some ψ ∈ Aut(G) and a ∈ G satisfy ψ(S) = aS⁻¹, then
   ψ(S)⁻¹ψ(S) = SS⁻¹, so ψ maps (S⁻¹S)^κ onto (SS⁻¹)^κ and the two conditions are equivalent. (If ψ(S) = S⁻¹a, then
   ψ maps (S⁻¹S)^κ onto a⁻¹(SS⁻¹)^κ a, with the same conclusion.) For abelian G, ψ = inversion always works. No checker
   uses this.
4. The sufficiency directions of (a) and (b) are formalised in Lean, in general as `haar_ediam_le_even` and
   `haar_ediam_le_odd` (`lean/BipartiteDD/Haar/GraphD.lean`). The record proofs use per-diameter lemmas that formalise
   the same direction: `isBipartiteDegDiam8_even_of` (`Haar/D9D8/Even8.lean`, through `haar_ediam_le_even`) for (9,8);
   `isBipartiteDegDiam_eight_equiv` (`Haar/D7D8/Diam8.lean`) for (7,8) and (8,8), which takes three covers (A–A, B–B
   and A–B), a stronger certificate than (a) needs; `haar_isBipartiteDegDiam9_of_equiv` (`Haar/Diam9.lean`) for (6,9)
   and (7,9); and `haar_isBipartiteDegDiam10_of_equiv` (`Haar/Diam10.lean`) for (4,10), (5,10) and (6,10). All use
   the convention of Definition 1.1 (`Haar/Graph.lean`). The record proofs supply, for every x ∈ G, an explicit word;
   the kernel checks the words (`decide +kernel`, no `native_decide`).

### 2.5 What each checker computes, and which statement makes it exact

| program | written independently of the search? | what it does | exact because of |
|---|---|---|---|
| `research/frontier/build_haar2.py` | yes | builds the field from addition/multiplication tables and checks associativity, distributivity and commutativity on 20,000 random triples and every inverse; enumerates SL/PSL/PGL(2, q) by brute force over all (a, b, c, d) and checks the order against the formula; builds the Δ permutations g ↦ sg of G and checks each is a permutation; BFS from (e, A) and from (e, B); requires every vertex reached within D, maximum degree Δ, no repeated edge; prints the sha256 of the edge list | Lemma 1.2, Cor. 2.3 |
| `research/frontier/check_haar_indep.py` | yes (its own field, matrix and enumeration code) | same two searches | Cor. 2.3 |
| `research/frontier/haarcheck_sl.c`, `research/frontier/haarcheck2.c` | yes (two separate C programs) | G = SL(2, p) × Z_n, p prime only; own indexing of SL(2, p), explicit 2 × 2 products mod p, inverse generators computed as [[d, −b], [−c, a]] and −z; bitset BFS from (e, A) and (e, B), about 4–6 bits of memory per group element | Cor. 2.3 |
| `research/structured/tools/haarcheck_psl.c` | yes, but modelled on `haarcheck_sl.c` (its header says so) | the same for PSL(2, p) × Z_n, p an odd prime | Cor. 2.3 |
| `research/theorems/haar_d8_10/hc_factor.c` | yes (written for this note) | SL(2, p) or PSL(2, p) times Z_n, p prime: permutation tables of the matrix factor (§5.3), then the same two searches | Cor. 2.3 |
| `research/lifts/coordinator_check/apsp.c`, `apsp_mt.c` | yes | BFS from **every** vertex of an edge list; checks simple, maximum degree, bipartite, connected and the exact diameter; no symmetry assumed | definition |
| Lean 4 (`lean/BipartiteDD/Haar/`) | yes | proves `IsBipartiteDegDiam G Δ D` for the specific graph, from a certificate of words, via lemmas that formalise the sufficiency direction of Theorem 2.4 for D = 8, 9, 10 (Remark 4) | Thm. 2.4 (formalised) |

The search programs (`haar_gen3.c`, `haar_fast.c`, `haar_sym.c`) also run a full two-source check before writing a
solution. We do not count that check as independent.

**What no checker uses.** None of the checkers uses the orbit symmetry α of §3. A solution file with f = 0 (§3) stores
T = S·s₀⁻¹ for an α-closed S and some s₀ ∈ S (Lemma 3.1(ii)), and T is not closed under any automorphism of the
searched form (computer-checked: `orbit_check.py` tries this first, exhaustively over the conjugating element and the
scaling). Instead α(T)·τ = T for τ = α(s₀)s₀⁻¹, which lies in T because α(s₀) ∈ S; indeed
α(S s₀⁻¹)·α(s₀)s₀⁻¹ = S s₀⁻¹. `orbit_check.py` and `orbit_check2.py` find such α and τ ∈ T for every f = 0 record
(§5; the logs print τ as c). That T has this form does not by itself give an α-closed S: one needs an s₀ with
α(s₀)s₀⁻¹ = τ, and then S = T s₀. For α(x, z) = (gxg⁻¹, rz) the equation splits into gXg⁻¹X⁻¹ = τ_Q in the matrix
factor (in each factor, for products) and (r − 1)z = τ_z in Z_n. `research/theorems/haar_d8_10/s0_check.py` solves it
in all 11 f = 0 files and finds solutions in each; in the matrix part they form a coset X₀·C_Q(g), so there are
|C_Q(g)| of them. For every solution, S = T s₀ satisfies α(S) = S with the cycle sizes stated in §5.1
(`recheck/s0_check.log`). So the validity of a record does not depend on any claim in §3: the symmetry was a search
device only.

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
   r ∈ Z_n^× of multiplicative order k. Here Fix(α) = C_Q(g) × {z : (r − 1)z = 0}. If r ≢ 1 (mod p) for every prime
   p | n (for prime k this is possible exactly when every prime factor of n is ≡ 1 mod k), then r − 1 is a unit mod n
   and the Z_n-part of Fix(α) is {0}; this holds for every k = 3 and k = 5 record except (7,8), where n = 14 and
   z ∈ {0, 7} are fixed. Let g ∈ SL(2, q) have order k ≥ 3 modulo the centre {±I}, with the characteristic not
   dividing k (for q odd and k = 3, g itself may have order 6, as in Appendix A). Then |C_{SL(2,q)}(g)| = q ± 1 (a
   torus) and, for q odd, the centraliser of the image of g in PSL(2, q) has order (q ± 1)/2 (for q even, PSL = SL).
   Why (q ± 1)/2 and not q ± 1: X ∈ SL(2, q) centralises the image of g iff XgX⁻¹ = ±g, and XgX⁻¹ = −g would give
   tr g = −tr g, i.e. tr g = 0; but tr g = 0 gives g² = −I (Cayley–Hamilton), so the image of g would have order
   ≤ 2. Hence only the sign + occurs, and the PSL centraliser is C_{SL(2,q)}(g)/{±I}. For products
   Q = Q_1 × Q_2, g = (g_1, g_2) and the centraliser is the product of the two. This is the k = 3 recipe of most
   records, and k = 5 for (11,8) and (11,10).
2. **Order 6 with a swap** on SL(2,7)² × Z_31 (the (13,8) record): α(x_1, x_2, z) = (g x_2 g⁻¹, x_1, 6z) with g of order 3.
   Since 6 has order 6 mod 31 and α² is conjugation by (g, g) times z ↦ 36z = 5z, α has order 6.
3. **An involution** on PSL(2,11) × Z_24 (the (6,8) record): conjugation by an involution times z ↦ 11z. Here the
   centraliser in PSL(2,11) is dihedral and the Z_24-part of Fix(α) is {0, 12}.

### 3.3 Equivariance

**Proposition 3.3.** Let α ∈ Aut(G) with α(S) = S, and let α̂(g, X) = (α(g), X).

(a) α̂ is an automorphism of H(G, S) that fixes (e, A) and (e, B). Together with the right translations it generates a
group of order |G|·ord(α), isomorphic to G ⋊ ⟨α⟩ via h ↦ ρ_{h⁻¹}, α ↦ α̂ (note ρ_hρ_{h′} = ρ_{h′h} and
α̂ρ_hα̂⁻¹ = ρ_{α(h)}).

(b) For every j ≥ 0 the sets (S⁻¹S)^j, S(S⁻¹S)^j, (SS⁻¹)^j and S⁻¹(SS⁻¹)^j are α-invariant. For every integer L ≥ 0 and
X, Y ∈ {A, B}, the set U of elements x such that (x, X) is at distance > L from (e, Y) is a union of ⟨α⟩-orbits.

(c) If k = ord(α) is prime, then |U| ≡ |U ∩ Fix(α)| (mod k).

(d) α permutes the letters of S by some permutation σ. Applying σ letterwise maps reduced A-words (B-words) of length
L bijectively to reduced A-words (B-words) of length L, and (σw)(S) = α(w(S)).

*Proof.* (a) The edge {(g, A), (sg, B)} maps to {(α(g), A), (α(s)α(g), B)}, an edge because α(s) ∈ S; α̂ is a
bijection with inverse (α⁻¹)^. It fixes (e, X) because α(e) = e. And α̂ρ_hα̂⁻¹(g, X) = (α(α⁻¹(g)h), X) =
(gα(h), X). The elements ρ_hα̂^i are pairwise distinct: ρ_hα̂^i = id forces h = e (evaluate at (e, A)) and then α^i = id;
so the group has order |G|·ord(α). (b) α((S⁻¹S)^j) = (α(S)⁻¹α(S))^j = (S⁻¹S)^j, and similarly for the others. For U:
α̂ is an automorphism fixing (e, Y), so d((e, Y), (α(x), X)) = d((e, Y), (x, X)). (c) The ⟨α⟩-orbits in U have size 1
(the points of Fix(α)) or k.
(d) σ is a bijection of S, so it preserves "t_{i+1} ≠ t_i", and α is a homomorphism. ∎

The number W(Δ, D) of binding words does not depend on S at all. What α(S) = S changes is that coverage is constant on
⟨α⟩-orbits: an element is covered exactly when all of its orbit is. Whether this makes S more or less likely to be valid
is a question about the model of §3.5, not a consequence of Proposition 3.3.

### 3.4 Involutions in the symmetry group, and why odd order was preferred

For an automorphism β put Anti(β) = {u ∈ G : β(u) = u⁻¹}.

**Proposition 3.4.**

(a) *(Reflection.)* Let β ∈ Aut(G) with β(S) = S, inducing σ on S. Let v = (t_1, …, t_{2j}) be a letter sequence of even
length and let v* = (σ(t_{2j}), …, σ(t_1)). Evaluate both with the same sign pattern (both as A-words, or both as
B-words). Then v*(S) = β(v(S))⁻¹. Hence v*(S) = v(S) if and only if v(S) ∈ Anti(β). The sequence v* is reduced iff v
is. If moreover β² = id, then v** = v, and v* = v iff t_{2j+1−i} = σ(t_i) for all i.

(b) *(Uncertainty.)* Let α ∈ Aut(G) have order k and put N_α(u) = u·α(u)⋯α^(k−1)(u). Then
|{u ∈ G : N_α(u) = e}| ≥ |G|/|Fix(α)|. For an involution β this reads |Fix(β)|·|Anti(β)| ≥ |G|.

(c) *(Odd order.)* If α has odd order, then Anti(α) = {u ∈ Fix(α) : u² = e}, the elements of order ≤ 2 in Fix(α).

*Proof.* (a) As A-words, v(S) = t_{2j}⁻¹ t_{2j−1} ⋯ t_2⁻¹ t_1, so v(S)⁻¹ = t_1⁻¹ t_2 ⋯ t_{2j−1}⁻¹ t_{2j}, which is the
A-word value of the reversed sequence (t_{2j}, …, t_1). Applying β letterwise gives β(v(S)⁻¹) = v*(S). The B-word case
is the same computation with all signs flipped. The other claims are immediate (σ is a bijection, so
σ(t_{i+1}) ≠ σ(t_i) iff t_{i+1} ≠ t_i; and σ² = id when β² = id).

(b) Let L(x) = x⁻¹α(x). The product N_α(L(x)) telescopes to x⁻¹α^k(x) = e. And L(x) = L(y) iff
yx⁻¹ = α(y)α(x)⁻¹ = α(yx⁻¹), i.e. iff y ∈ Fix(α)x. So the fibres of L are the cosets Fix(α)x, and L has
|G|/|Fix(α)| distinct values, all with N_α = e. For k = 2, N_β(u) = e iff β(u) = u⁻¹.

(c) If α(u) = u⁻¹ then α²(u) = α(u)⁻¹ = u. Since k is odd, α = (α²)^((k+1)/2), so α(u) = u, and then u = u⁻¹. The
converse is clear. ∎

*What this means for the search.* Let w be a binding word and v a block of consecutive letters of w of even length,
evaluated with the sign pattern of its position in w (A-pattern if it starts at an odd position, B-pattern if at an
even one). If ⟨α⟩ contains an involution β, v(S) ∈ Anti(β) and v* ≠ v, then by (a) the word w′ obtained by replacing v
by v* has the same value as w. If w′ is reduced, two distinct binding words share a value; if not, that value is also
the value of a shorter reduced word. By (b), Anti(β) has at least |G|/|Fix(β)| elements; for conjugation times a scaling on
SL(2, q) × Z_n whose Z_n-part of Fix(β) is bounded, that is a fraction of order 1/q of the group. A group of odd order contains no involution (Lagrange),
and by (c) even the elementwise condition α(u) = u⁻¹ is then confined to the elements of order ≤ 2 in Fix(α). Odd k
still gives exact relations from (b): if N_α(u) = e for the value u of an even block of length L, then
u⁻¹ = α(u)α²(u)⋯α^(k−1)(u), so the reversed block (value u⁻¹, length L) and a block of length (k − 1)L, possibly not
reduced, have the same value. That these relations cost far fewer binding words than the reflections of (a), and how
many words each mechanism costs in practice, is **heuristic and measured**
(research/theory/BEYOND_RANDOM.md §1.4, §4.2).

Two records show that "prefer odd k" is a heuristic preference, not a theorem. At (6,8) an involution won, and at
(13,8) an automorphism of order 6 won (research/theorems/ORDER2.md on branch `claude/thm-order2-symmetry-wejgw7`).
ORDER2.md §2.1 proves that each coincidence of (a) is a closed walk v·σ(v) of the graph (a "twisted cycle"), and
**measures** (§3.1 there) that these concentrate on a few short cycles, which a solution can avoid, rather than costing
a fixed fraction of all words.

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
| (7,8) | PSL(2,19) × Z_13 | 44,460 | 23.3 | 1/4 | 4/4 (737 to 3,625 evaluations) |
| (7,8) | PSL(2,17) × Z_19 | 46,512 | 34.0 | 0/4 (best cost 6 after 1.2–1.6·10⁶ evaluations) | 4/4 (1.7–5.8·10⁴) |
| (7,8) | PSL(2,19) × Z_14 | 47,880 | 43.0 | 0/4 (best 9–10) | 1/4 (2.3·10⁵) |

Over 32 solved orbit runs, the number of evaluations fits the random-S effort law of research/frontier/SIZE_LAW.md
§4.1 with μ_A in place of μ (BEYOND_RANDOM.md §2).

*What does not change.* For f ≥ 1 (so e ∈ S) the number of α-closed sets is about (N/k)^m/m! · C(|Fix(α)| − 1, f − 1);
for f = 0 there are about (N/k)^m/m! α-closed sets, giving about Δ times as many translates containing e. All sets
containing e number C(N − 1, Δ − 1) ≈ N^(Δ−1)/(Δ − 1)!. Setting the expected number of valid sets to 1 gives a
"first-moment ceiling" of μ ≈ km·ln N = (Δ − f) ln N for α-closed sets (with P(valid) ≈ e^(−μ/k)) and μ ≈ (Δ − 1) ln N
for all sets, to leading order. The two differ by (f − 1)·ln N, by the |Fix(α)| term (they agree when |Fix(α)|^k ≈ N)
and by factorials, which are not negligible at the sizes of §5 (STRUCTURE.md §1; BEYOND_RANDOM.md §1.5 computes the
margins). So in this model orbit-closure makes larger groups *searchable*; it
does not make larger valid sets *exist*. Cells whose table value lies above that ceiling (for example (12,8), (14,8),
(16,8)) were not reached, consistent with the model (STRUCTURE.md §6).

---

## 4. Counting bounds and family statements

### 4.1 The per-side Moore bound

**Theorem 4.1.** If |S| = Δ ≥ 2 and diam H(G, S) ≤ D, then |G| ≤ W(Δ, D) = Σ_{j=0}^{D−1} (Δ − 1)^j.

*Proof.* A shortest path never backtracks, so by Proposition 2.2 every element at distance L from (e, A) is the value of
a reduced A-word of length L, and there are at most Δ(Δ − 1)^(L−1) of them for L ≥ 1.
If D = 2κ, Theorem 2.4(a) puts every (x, B) at odd distance ≤ 2κ − 1 from (e, A), so

$$|G| \le \sum_{i=0}^{\kappa-1}\Delta(\Delta-1)^{2i} = \sum_{i=0}^{\kappa-1}\big[(\Delta-1)^{2i}+(\Delta-1)^{2i+1}\big] = \sum_{j=0}^{2\kappa-1}(\Delta-1)^j .$$

If D = 2κ + 1, Theorem 2.4(b) puts every (x, A) at even distance ≤ 2κ from (e, A), so

$$|G| \le 1+\sum_{i=1}^{\kappa}\Delta(\Delta-1)^{2i-1} = 1+\sum_{i=1}^{\kappa}\big[(\Delta-1)^{2i-1}+(\Delta-1)^{2i}\big] = \sum_{j=0}^{2\kappa}(\Delta-1)^j . \qquad ∎$$

Theorem 4.1 is exactly the bipartite Moore bound 2|G| ≤ M^b(Δ, D); we include it because the same count, the number
W(Δ, D) of binding words, is the quantity behind every estimate in §3.5. It uses only one of the two conditions at odd D.

**Corollary 4.2 (cited).** For Δ ≥ 3 and D ∈ {8, 9, 10}, the inequality in Theorem 4.1 is strict.

*Proof.* Suppose |G| = W(Δ, D). The proof of Theorem 4.1 shows that the reduced A-words of the binding parity and length
≤ D − 1 cover G; there are exactly W(Δ, D) of them, so their values are pairwise distinct.

*Girth.* Suppose H(G, S) has a cycle of length 2γ < 2D. Every cycle passes through an A-vertex, and a right translation
moves it to (e, A). The two arcs of the cycle from (e, A) to the opposite vertex are distinct paths of length γ, hence
two distinct reduced A-words of length γ with the same value. Their last letters differ, because the two arcs enter
the opposite vertex along different edges and the edges at a vertex carry different letters. If γ ≡ D − 1 (mod 2),
then γ ≤ D − 1 contradicts distinctness. Otherwise γ ≤ D − 2; since Δ ≥ 3 there is a letter t different from both last
letters, and appending t gives two distinct reduced words of length γ + 1 ≤ D − 1, of the binding parity, with the same
value, again a contradiction. So the girth is at least 2D.

Below we use one standard fact twice: (∗) if P and P′ are distinct paths with the same two ends, then P ∪ P′ contains a
cycle of length at most |P| + |P′|. A finite graph of minimum degree ≥ 2 has a cycle, and a graph of diameter ≤ D
containing a cycle has girth ≤ 2D + 1: on a shortest cycle C of length ≥ 2D + 2, take two vertices joined by an arc of
C of length D + 1 (the other arc is at least as long); a shortest path between them has length ≤ D, so it differs from
that arc, and by (∗) they contain a cycle of length ≤ 2D + 1, shorter than C. Being bipartite, H(G, S) therefore has
girth ≤ 2D, so its girth is exactly 2D. Then the diameter is exactly D: let u, v be opposite vertices of a cycle C of
length 2D, so that both arcs of C between them have length D. If d(u, v) < D, a shortest u–v path differs from both
arcs, and by (∗) it and one arc contain a cycle of length < 2D, which is impossible.

*Polygons.* A bipartite graph with diameter D, girth 2D and all degrees ≥ 3 is the incidence graph of a thick
generalized D-gon (Tits' definition); here of order (Δ − 1, Δ − 1). By the Feit–Higman theorem (J. Algebra 1 (1964)
114–131) thick generalized n-gons exist only for n ∈ {2, 3, 4, 6, 8}, and a generalized octagon of order (s, t) needs 2st
to be a perfect square, which fails for s = t. So D ∉ {8, 9, 10}. *The Feit–Higman theorem is cited, not reproved.* ∎

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

For fixed Δ, A(Δ, D) = Θ(D^(Δ−1)): it is a polynomial of degree Δ − 1 in D on each parity class of D (for example
A(3, D) = 3D²/4 for D even and (3D² + 1)/4 for D odd), while W(Δ, D) is exponential in D. *Reason.* Write
c = c⁺ − c⁻ with c⁺, c⁻ ≥ 0 of disjoint supports; then Σc⁺ = j + ε and Σc⁻ = j for some j with
0 ≤ j ≤ K = ⌊(D − 1 − ε)/2⌋, and K = (D − 2)/2 or (D − 1)/2 is linear in D on each parity class. The terms with j = 0
contribute a constant (Δ vectors if ε = 1, one if ε = 0). For j ≥ 1 both supports are non-empty, and for supports of
sizes a and b (a, b ≥ 1, a + b ≤ Δ) there are C(j + ε − 1, a − 1)·C(j − 1, b − 1) such c, a polynomial in j of degree
a + b − 2. Summing over the supports and over 1 ≤ j ≤ K gives a polynomial in K of degree Δ − 1, with positive leading
coefficient from the terms with a + b = Δ. Values (computed by a short dynamic program,
`research/theorems/haar_d8_10/abound.py`):

| Δ | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| A(Δ, 8) | 48 | 216 | 780 | 2,376 | 6,328 | 15,128 | 33,111 | 67,360 | 128,876 | 234,048 | 406,458 | 679,056 | 1,096,740 | 1,719,376 |
| A(Δ, 9) | 61 | 309 | 1,251 | 4,251 | 12,559 | 33,111 | 79,459 | 176,251 | 365,751 | 716,959 | 1,337,961 | 2,392,209 | 4,119,501 | 6,862,501 |
| A(Δ, 10) | 75 | 420 | 1,875 | 7,002 | 22,645 | 65,080 | 169,515 | 406,390 | 907,753 | 1,907,940 | 3,803,865 | 7,241,430 | 13,235,895 | 23,335,504 |

**Corollary 4.4.** Under the hypotheses of Theorem 4.3:

(i) if G is abelian, |G| ≤ A(Δ, D);

(ii) if G = Q × Z_n with Q perfect (Q = Q′), then n ≤ A(Δ, D). This applies to Q = SL(2, q) and PSL(2, q) with
q ≥ 4, and to direct products of such groups;

(iii) if G = Z_m ⋊_r Z_ℓ, then G′ = (r − 1)Z_m × {0} and ℓ·gcd(m, r − 1) ≤ A(Δ, D).

*Proof.* (i) G′ = 1. (ii) G′ = Q′ × {0} = Q × {0}, so G/G′ ≅ Z_n. SL(2, q) is perfect for q ≥ 4 and PSL(2, q) is simple
for q ≥ 4 (standard); a direct product of perfect groups is perfect. (iii) Conjugating (a, 0) by (0, 1) gives (ra, 0),
so G′ contains the commutators ((r − 1)a, 0), i.e. (r − 1)Z_m × {0}. That subgroup is normal (it is stable under
multiplication by r), and the quotient is Z_d × Z_ℓ with d = gcd(m, r − 1) and trivial action (r ≡ 1 mod d), which is
abelian. So G′ = (r − 1)Z_m × {0} and |G/G′| = dℓ. ∎

For example, the (8,8) record PSL(2,17) × Z_49 has n = 49 ≤ A(8,8) = 15,128, and the metacyclic records have
|G/G′| = 80, 70, 64, 24 at (5,8), (5,9), (4,10), (5,10), against A = 780, 1,251, 420, 1,875. Used as an obstruction,
the corollary says that at small Δ an abelian group, or a group with a large abelian quotient, cannot reach record
size. For instance an abelian Haar graph of degree 8 and diameter 8 has at most 2·15,128 = 30,256 vertices, against the
table's 201,480. It forces only |G′| ≥ |G|/A(Δ, D) (at least 8 at (8,8), at least 91 at (16,10)); that the SL/PSL-type record
groups have perfect parts of order 660 to 7.9·10⁶ (and the metacyclic ones commutator subgroups of order 61 to 1,989) is
a search choice, guided by the heuristics of §3.5 and §4.3, not a consequence of Theorem 4.3.

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
(q(q ± 1)/2 involutions for q odd) is a poor choice at odd D and SL(2, q) with q odd (one involution, −I) a good one
(research/theory/THRESHOLD.md §3, Corollary 5.2 for a proved version in the regime D fixed, Δ → ∞). Every odd-D record
in §5 uses SL(2, q), a product containing SL(2, q), a PSL(2, q) with a cyclic factor of odd order, or a metacyclic group.

### 4.4 A provable lift family at D = 8 (not Haar graphs)

**Proposition 4.6** (research/theorems/D8_NUMEROLOGY.md §1.1, branch `claude/d8-table-numerology-mi6but`). Let B be a
bipartite graph with colour classes P (points) and L (lines) of equal size and diameter at most δ, δ even. Let
s_1, …, s_J be bijections P → L and t_1, …, t_J ∈ Z_n. Let X have vertex set V(B) × Z_n, with the edges
(u, z) ~ (v, z) for uv ∈ E(B) (copy z of B) and the *hops* (p, z) ~ (s_i(p), z + t_i) for p ∈ P and every i. If

Z_n = {0} ∪ {±t_i} ∪ {t_i − t_j : i ≠ j} ∪ {t_i + t_j : i ≤ j}   (i = j is allowed in the last set),

then X has diameter at most δ + 2.

*Proof.* Inside one copy, vertices on the same side are at distance ≤ δ and vertices on opposite sides at distance
≤ δ − 1. A hop goes from a point of copy z to a line of copy z + t_i, or from a line of copy z to a point of copy
z − t_i, and since s_i is a bijection its far end can be prescribed. Let u be in copy z and v in copy z + d. A
line–point pair is a point–line pair with d replaced by −d, which is again in the set, so we may take u, v to be two
points, a point and a line, or two lines. Each entry below is a walk from u to v: "≤ a" is a path of length ≤ a inside
the current copy, "h" a hop, "1" an edge of a copy, and the intermediate targets are chosen so that the walk ends at v
(for example, for two lines and d = t_i + t_j: inside copy z to the point s_i⁻¹(m), where m is a line through the
point s_j⁻¹(v); hop to m; one edge to s_j⁻¹(v); hop to v).

| d | point to point | point to line | line to line |
|---|---|---|---|
| 0 | ≤ δ | ≤ δ − 1 | ≤ δ |
| t_i | h, ≤ δ − 1 (δ) | ≤ δ, h (δ + 1) | ≤ δ − 1, h (δ) |
| −t_i | ≤ δ − 1, h (δ) | ≤ δ − 1, h, 1 (δ + 1) | ≤ δ, h, 1 (δ + 2) |
| t_i − t_j | h, ≤ δ, h (δ + 2) | ≤ δ − 1, h, h (δ + 1) | ≤ δ, h, h (δ + 2) |
| t_i + t_j | h, ≤ δ − 1, h, 1 (δ + 2) | h, ≤ δ − 1, h (δ + 1) | ≤ δ − 1, h, 1, h (δ + 2) |

In the row t_i − t_j the point-to-point walk hops by +t_i and then by −t_j; the other two hop by −t_j and then by +t_i.
Every length is at most δ + 2. ∎

Applied to generalized hexagons (δ = 6) this gives diameter-8 graphs; D8_NUMEROLOGY.md §1.1 tabulates their orders,
which are below the table in every cell.

### 4.5 What we cannot prove

- **No infinite family at fixed D.** We have no theorem that produces, for D ∈ {8, 9, 10}, an infinite family of Haar
  graphs (or any graphs) above the table. Each record in §5 is a single graph.
- **The size law is not a theorem.** The observed orders follow N ≈ Δ(Δ − 1)^(D−2) g_Δ / ln(N/μ\*) with a slowly varying
  μ\* (SIZE_LAW.md; g_Δ = (Δ−1)²/((Δ−1)² − 1)). That is a heuristic fitted to data.
- **Random-S theorems are in another regime.** research/theory/THRESHOLD.md proves, for every finite group and fixed D
  as Δ → ∞, that a random S of size Δ gives diameter ≤ D with high probability once the number of distinct-letter words
  exceeds (1 + η)(D−1)!·N ln N for a fixed η > 0, and fails below N(ln N − ln ln N − ω(1)). The two bounds differ by
  the factor (D − 1)!, so this is a window, not a sharp threshold. Those proofs use Suen's inequality (in the form
  stated by Yadin) and are not reproduced here. They say nothing about fixed Δ ≤ 16, the regime of the records.

---

## 5. Records at D = 8, 9, 10

**Status.** Every entry below is a **computer-checked record, not a theorem**: one explicit graph, checked by programs.
Where the Lean column has ✓, the same graph (same group and generators, compared against the file) is also proved in
Lean 4, so for that graph the statement "bipartite, maximum degree ≤ Δ, diameter ≤ D, this many vertices" is a
kernel-checked theorem. "Gain" is measured against the 2013 table (§1.1). The order is also given as a fraction of the
bipartite Moore bound.

*Date of the values.* The table gives the records as of master commit `294fc94` (25 Oct 2026), which the repository
README matches. A later master commit (`c48c976`) records larger graphs at (9,8) (546,720 vertices, SL(2,16) × Z_67)
and at (5,9) (29,756 vertices, Z_346 ⋊_29 Z_43) in `research/RESULTS.md`. They are later than this table and are not
part of this note's checks.

### 5.1 The records

<!-- TABLE (generated by research/theorems/haar_d8_10/make_table.py from the logs in haar_d8_10/recheck/) -->
| cell | 2013 table | ours | gain | of Moore bound | group G | orbit structure of S (verified) | Lean | checks before today | this session |
|---|---:|---:|---:|---:|---|---|:---:|---|---|
| (3,8) | 256 | **288** | +12.5 % | 56.5 % | lift of a 4-vertex base over Z_3² ⋊ Z_8 (note 1) | – | ✓ | apsp | apsp |
| (5,8) | 9,234 | **9,760** | +5.7 % | 22.3 % | Z_61 ⋊_8 Z_80 | – | (9,576) | bh2 | bh2, apsp |
| (6,8) | 29,790 | **31,680** | +6.3 % | 16.2 % | PSL(2,11) × Z_24 | k = 2, f = 0: 2+2+2 | (30,576) | bh2 | bh2, ind, hcf, apsp |
| (7,8) | 80,940 | **95,760** | +18.3 % | 14.3 % | PSL(2,19) × Z_14 | k = 3: 1+3+3 | ✓ | bh2 ×2 | bh2, ind, hcf, apsp |
| (8,8) | 201,480 | **239,904** | +19.1 % | 12.5 % | PSL(2,17) × Z_49 | k = 3: 1+1+3+3 | ✓ | bh2 ×2 | bh2, ind, hcf, apsp |
| (9,8) | 449,480 | **540,360** | +20.2 % | 11.3 % | PSL(2,19) × Z_79 | k = 3, f = 0: 3+3+3 | ✓ | bh2 ×2 | bh2, ind, hcf, apsp |
| (11,8) | 2,246,940 | **2,258,520** | +0.5 % | 10.2 % | PSL(2,59) × Z_11 | k = 5: 1+5+5 | – | bh2, ind, hpsl, big | bh2, hcf |
| (13,8) | 5,314,680 | **6,999,552** | +31.7 % | 9.0 % | SL(2,7)² × Z_31 | k = 6 (swap): 1+6+6 | – | bh2, big (+3 on a branch) | bh2, ind |
| (15,8) | 14,172,480 | **18,128,880** | +27.9 % (+21.0 %, note 4) | 8.0 % | SL(2,109) × Z_7 | k = 3, f = 0: 3+3+3+3+3 | – | bh2, hsl, big | bh2, ind, hcf |
| (5,9) | 27,936 | **29,540** | +5.7 % | 16.9 % | Z_422 ⋊_5 Z_35 | – | (28,560) | bh2 | bh2, apsp |
| (6,9) | 117,360 | **127,296** | +8.5 % | 13.0 % | SL(2,17) × Z_13 | k = 3, f = 0: 3+3 | ✓ | bh2 ×2 | bh2, ind, hcf, apsp |
| (7,9) | 400,160 | **462,840** | +15.7 % | 11.5 % | PSL(2,29) × Z_19 | k = 3: 1+3+3 | ✓ | bh2 ×3 | bh2, ind, hcf, apsp |
| (8,9) | 1,091,232 | **1,341,600** | +22.9 % | 10.0 % | SL(2,25) × Z_43 | k = 3: 1+1+3+3 | – | bh2 | bh2, ind |
| (9,9) | 2,961,536 | **3,499,776** | +18.2 % | 9.1 % | PSL(2,7) × SL(2,7) × Z_31 | k = 3, f = 0: 3+3+3 | – | bh2 ×2, big | bh2, ind |
| (10,9) | 7,057,400 | **8,003,856** | +13.4 % | 8.3 % | SL(2,83) × Z_7 | k = 3: 1+3+3+3 | – | bh2, ind, hsl, hc2, big | bh2, hcf |
| (11,9) | 15,200,448 | **16,792,080** | +10.5 % | 7.6 % | SL(2,61) × Z_37 | k = 3: 1+1+3+3+3 | – | bh2, ind, hsl, hc2, big | bh2, hcf |
| (12,9) | 30,001,152 | **34,026,720** | +13.4 % | 7.2 % | SL(2,41) × Z_247 | k = 3, f = 0: 3+3+3+3 | – | hsl, hc2, big | hsl, hcf |
| (13,9) | 50,990,610 | **67,742,688** | +32.9 % | 7.2 % | SL(2,103) × Z_31 | k = 3: 1+3+3+3+3 | – | hsl, big | hsl, hc2, hcf |
| (14,9) | 95,087,738 | **116,068,656** | +22.1 % | 6.6 % | SL(2,67) × Z_193 | k = 3: 1+1+3+3+3+3 | – | hsl, hc2, big | hsl, hcf |
| (15,9) | 168,016,334 | **208,029,120** | +23.8 % | 6.5 % | SL(2,79) × Z_211 | k = 3, f = 0: 3+3+3+3+3 | – | hsl, hc2, big | hsl, hcf |
| (16,9) | 288,939,118 | **337,394,400** | +16.8 % | 6.1 % | SL(2,151) × Z_49 | k = 3: 1+3+3+3+3+3 | – | hsl, hc2, big (note 3) | hsl, hcf |
| (4,10) | 11,748 | **12,416** | +5.7 % | 21.0 % | Z_97 ⋊_19 Z_64 | – | ✓ | apsp | apsp |
| (5,10) | 90,068 | **95,472** | +6.0 % | 13.7 % | Z_1989 ⋊_461 Z_24 | – | ✓ | apsp | apsp |
| (6,10) | 452,032 | **524,160** | +16.0 % | 10.7 % | SL(2,5) × PSL(2,7) × Z_13 | k = 3, f = 0: 3+3 | ✓ | bh2 ×2 | bh2, ind, apsp |
| (7,10) | 1,987,380 | **2,237,760** | +12.6 % | 9.3 % | PSL(2,5) × SL(2,8) × Z_37 | k = 3: 1+3+3 | – | bh2, big | bh2, ind |
| (8,10) | 6,927,210 | **7,818,096** | +12.9 % | 8.3 % | SL(2,67) × Z_13 | k = 3: 1+1+3+3 | – | hsl, big | bh2, ind, hc2, hcf |
| (9,10) | 20,017,260 | **23,975,280** | +19.8 % | 7.8 % | PSL(2,71) × Z_67 | k = 3, f = 0: 3+3+3 | – | hpsl ×2, big | ind, hpsl, hcf |
| (10,10) | 50,331,156 | **60,141,120** | +19.5 % | 6.9 % | SL(2,79) × Z_61 | k = 3: 1+3+3+3 | – | hsl, hc2, big | hsl, hcf |
| (11,10) | 130,592,354 | **148,729,680** | +13.9 % | 6.7 % | PSL(2,89) × Z_211 | k = 5: 1+5+5 | – | hpsl, big | hpsl, hcf |
| (12,10) | 300,383,050 | **325,832,976** | +8.5 % | 6.3 % | SL(2,107) × Z_133 | k = 3, f = 0: 3+3+3+3 | – | hsl, hc2, big | hsl, hcf |
| (13,10) | 617,330,936 | **677,714,400** | +9.8 % | 6.0 % | SL(2,199) × Z_43 | k = 3: 1+3+3+3+3 | – | hsl, hc2, big | hcf |
| (14,10) | 1,213,477,190 | **1,326,627,120** | +9.3 % | 5.8 % | SL(2,139) × Z_247 | k = 3: 1+1+3+3+3+3 | – | hsl, hc2, big | hcf |
| (15,10) | 2,300,326,510 | **2,467,618,800** | +7.3 % | 5.5 % | SL(2,149) × Z_373 | k = 3, f = 0: 3+3+3+3+3 | – | hsl, big | hc2 |
| (16,10) | 4,119,507,330 | **4,220,872,800** | +2.5 % | 5.1 % | SL(2,151) × Z_613 | k = 3: 1+3+3+3+3+3 | – | hsl, big | hc2, hcf |
<!-- /TABLE -->

*Solution files.* `research/frontier/sols/<cell>_…txt`, one per cell; the stems are listed in `make_table.py`. Exceptions:
(3,8), (4,10) and (5,10) are in `research/lifts/sols/`.

*Orbit structure.* "k = 3: 1+3+3" means that S is closed under an automorphism α of order k of the form in
Construction 3.2, and α splits S into cycles of the sizes shown (1 = a fixed generator). "f = 0" means no fixed
generator; such files store a translate T (§2.5), and the entry describes S = T s₀, which gives an isomorphic graph
(Lemma 3.1(ii)). Each entry was verified from the file alone by `orbit_check.py` (single-factor groups over prime
fields) or `orbit_check2.py` (products, GF(25), and the order-6 swap of (13,8)); outputs in `recheck/orbit_check.log`
and `recheck/orbit_check2.log`. For the f = 0 rows these scripts verify that T is closed under x ↦ α(x)τ with the
stated cycle sizes, and `s0_check.py` then finds every s₀ with α(s₀)s₀⁻¹ = τ and checks that T s₀ is α-closed with the
same cycle sizes (`recheck/s0_check.log`, all 11 files). "–" means the graph was not found by an orbit search and no
symmetry is claimed.

*Checkers.* bh2 = `build_haar2.py`; ind = `check_haar_indep.py`; hsl = `haarcheck_sl.c`; hc2 = `haarcheck2.c`;
hpsl = `haarcheck_psl.c`; hcf = `research/theorems/haar_d8_10/hc_factor.c` (written for this note, see §5.3);
apsp = all-pairs BFS with `apsp.c` or `apsp_mt.c`, on an edge list built by `research/lifts/coordinator_check/build.py`
(its own group code) or by `build_haar2.py`; it reports the exact diameter, so it also fails, as it should, when asked
for D − 1 (for (7,9) that second run was cut off by a worker restart, `recheck/apsp.log`, after the exact diameter 9
had been reported); big = `bigcheck_indep.c` (cloud runs; its source is not in the repository, §5.2). These are
separately written programs, except that hpsl is a PSL variant of hsl (its header says it was modelled on
`haarcheck_sl.c`); no cell rests on hsl and hpsl alone, since every hpsl cell also has ind or hcf. hsl and hc2 are two
different C programs. "bh2 ×2" means the same program was run twice (by the search session and at harvest, with the
same edge-list sha256).

*Lean.* ✓ = a theorem `nb_Δ_D_…` in `lean/BipartiteDD/Haar/<dir>/Record*.lean` for this graph, with its own
`Axioms.out.txt` listing only `propext`, `Classical.choice`, `Quot.sound` (no `sorry`, no `native_decide`). A number in
brackets is the largest earlier (smaller) graph of the cell proved in Lean. These modules are not imported by the default
target `lean/BipartiteDD.lean`; build each with `lake build BipartiteDD.Haar.<dir>.<file>` (for example
`lake build BipartiteDD.Haar.D7D8b.Record`). The Lean builds were not re-run in this session; the `Axioms.out.txt` files
are those written when each proof was merged.

**Notes.**

1. (3,8) is the only record here that is not a Haar graph: a 72-fold regular cover of a cubic bipartite multigraph on
   2 + 2 vertices (edges 0–2 twice, 0–3, 1–2, 1–3 twice), with voltages in Z_3² ⋊_φ Z_8, where the generator of Z_8
   acts by φ = [[0, 2], [1, 0]] (`research/lifts/sols/c1r_d3D8_n288_b2_3_0_aff302108_s1.txt`). It is not isomorphic to
   a Haar graph either. In each colour class, 72 vertices have 91 vertices at distance 6 and 22 at distance 8, and the
   other 72 have 89 and 24 (`haar_d8_10/lift38_profiles.py`, `recheck/lift38_profiles.log`). So its automorphism group
   is not transitive on a colour class, whereas the right translations of a Haar graph are (Lemma 1.2(b)). For a cell
   this well studied, 288 against 256 is a large jump; the table audit found no source for 256 and no later value
   (`research/projects/table-audit/AUDIT.md` §3 and §5, and `research/projects/table-audit/lit/LITERATURE.md` §8, branch
   `claude/table-audit-1odopy`).
2. (11,10): the table value is 130,592,354 (§6.1), not 0 as the repository README says.
3. (16,9): the earlier cloud report `research/frontier/runs/cloudcheck/d16D9_sl_151_49_orb3_s1.txt` has a header copied
   from the (14,10) report (file name and sha256), while its checker output is for the (16,9) graph. The search session's
   own hsl and hc2 runs (`research/structured/runs/d16D9_sl_151_49_orb3_s1.log`) and this session's runs are for the right
   file.
4. (11,8): the table value is one of the D = 8 values from Gómez's ΩH_q that the table audit could not reproduce at
   diameter 8 (§6.1). (15,8): the table's 14,172,480 repeats the (14,8) value, and Gómez's thesis lists the larger
   value 14,978,080 there (§6.1). Against 14,978,080 our graph (18,128,880 vertices) is a gain of +21.0 %, not +27.9 %.
   Our graphs are checked either way; only the size of the gain is in question.

### 5.2 Gaps in the earlier record-keeping, and what this session did about them

An audit of the logs (2026-10-25) found the following. None of them affects whether a graph is valid; they affect how
well the evidence was recorded.

- **Single-program cells.** Before today, (5,8), (5,9), (6,8) and (8,9) had only one checker run each (build_haar2 at
  harvest), and (13,9), (7,10), (8,10), (11,10), (15,10), (16,10) had only one recorded run (a cloud job with two
  checkers, whose output the harvest log copies). This session re-ran every graph (column "this session"). After it,
  every cell has been accepted by at least two separately written programs, or by one program and a Lean proof.
- **`bigcheck_indep.c` is not in the repository**, nor its validation output, although it was the second checker for
  every graph above 2·10⁷ vertices. This is why `hc_factor.c` was written (§5.3): every large graph now has a second
  in-repository program. The cloud summary (`research/frontier/runs/cloudcheck/SUMMARY-bigcheck-3-verification-yp7r8n-big3.md`)
  notes that all checkers read the files with the same conventions. That cannot make an invalid record pass: each
  checker verifies the graph defined by that reading, which is the one stated in §1.4, and that graph is the record.
- **The harvest tool** (`labctl`) is not in the repository; its checks are only described in SIZE_LAW.md and old commit
  messages.
- **`check_haar_indep.py`** had been run on only three current records ((10,9), (11,9), (11,8)); this session ran it on
  the other 14 Haar records up to 2.4·10⁷ vertices that it can read (it does not read metacyclic groups).
- **Labels.** The README "Method" column calls (13,8), (7,10), (8,10), (11,10), (15,10) and (16,10) "finite geometry";
  all six are orbit-search Haar graphs (verified above). It calls (8,9) "evolutionary search"; the file is an orbit-closed
  Haar graph of SL(2,25) × Z_43. (5,8) and (5,9) are metacyclic Haar graphs; no log in the repository shows how they were
  found. It calls (3,8) "voltage lift / metacyclic Haar". It is a voltage lift, but not a Haar graph (note 1), and its
  group is not metacyclic: the commutator subgroup of Z_3² ⋊_φ Z_8 contains (φ − I)Z_3² = Z_3² (φ − I is invertible
  mod 3), which is not cyclic, whereas a metacyclic group has a cyclic commutator subgroup.

### 5.3 The checker written for this note

`research/theorems/haar_d8_10/hc_factor.c` handles G = Q × Z_n with Q = SL(2, p) or PSL(2, p), p prime. It enumerates Q by
brute force over all (a, b, c, d) ∈ [0, p)⁴ with ad − bc = 1 (for PSL keeping the lexicographically smaller of ±X),
checks |Q| against the formula, turns each generator (Y, t) into two permutation tables of Q (X ↦ YX and X ↦ Y⁻¹X),
checks that both are bijections, and runs the two searches of Corollary 2.3 on Q × Z_n with bitsets. It reads only the
`mat(…)` and `z=` fields of the file. It cannot read GF(q) for q not prime, products of two matrix groups, metacyclic
groups or the lift. It reports VALID on the 23 records it was run on to completion: every SL(2, p) × Z_n and
PSL(2, p) × Z_n record over a prime field except (15,10), whose run was cut off by a worker restart
(`recheck/hc_factor.log`). It reports INVALID on a file with one generator altered and on the (7,8) file with D lowered
to 7 (`recheck/hc_factor_negative.log`).

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

## 6. Prior art, and what this note contributes

Tags: **[read]** the lab read the primary source; **[secondary]** known from a survey, an abstract or a citation only;
**[inferred]** deduced from table values, not stated anywhere. Items taken from the lab's novelty check keep its finer
tags: **[meta]** bibliographic data only; **[abstract]** abstract or search snippet only; **[agent]** read by a helper
agent of that check and not re-read by its author. The literature notes behind this section are
`research/theory/LITERATURE.md`, `research/projects/table-audit/lit/LITERATURE.md` (branch `claude/table-audit-1odopy`)
and the novelty check `research/lit/novelty-2026-10-25.md` (branch `claude/novelty-literature-check-4i5frp`, claim 5).
As there, "nothing found" means only that the searches listed in the novelty check returned nothing. It is not evidence
that the thing has not been done.

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
- D = 8 with Δ = 10, 11, 12, 14, 16: J. Gómez Martí's thesis (UPC Barcelona, 1986, §2.9.3, pp. 45–46) lists exactly
  these table values as orders of a compound ΩH_q of generalized hexagons [read]. At Δ = 15 the table's 14,172,480 is
  the (14,8) value reused; the thesis lists the larger 14,978,080 there ("ΩH₁₁d"), which the wiki does not use
  (`research/projects/table-audit/AUDIT.md` §4, flag 1). The wiki credits the D = 8 cells with Δ ≥ 10 to
  Delorme–Gómez–Quisquater, "On large bipartite graphs", which was never published [secondary]. The lab's rebuild of
  ΩH_q as read from the thesis has the right order but diameter 9 (AUDIT.md §4). This may be a misreading of the
  thesis's figure, so we do not claim the values are wrong.
- (13,8) = 5,314,680 = 15·|H(11)| has no traced construction (D8_NUMEROLOGY.md on branch
  `claude/d8-table-numerology-mi6but` studies these numbers; it proves bounds for natural lift families but does not
  find the construction).
- **(11,10).** The survey PDF prints "130 592 1354"; every wiki revision has 130,592,354 (AUDIT.md §1). The repo README
  lists the table value as 0. The correct comparison is 130,592,354; our 148,729,680 is 13.9 % above it.
- **After 2013.** The wiki changed only at (13,3) and (15,3) (Araujo-Pardo–López). The table audit's literature search
  found no later paper with a larger bipartite graph at D = 8–10 (`research/projects/table-audit/lit/LITERATURE.md` §8).
  The novelty check found no bipartite table newer than the wiki's, which is "as of January 2012" [read]; the 2026
  updates of Comellas's table (arXiv:2406.18994v2 and the live pages) are for general graphs [read]. Neither search was
  exhaustive; the novelty check lists the sources it could not reach (Google Scholar and zbMATH were not queried).

**Haar graphs and lifts.** Haar graphs: M. Hladnik, D. Marušič, T. Pisanski, *Cyclic Haar graphs*, Discrete Math. 244
(2002) [secondary]; A. Estélyi, T. Pisanski, *Which Haar graphs are Cayley graphs?*, Electron. J. Combin. 23(3) (2016)
P3.10 [abstract]. A Haar graph is a regular cover of a dipole (standard voltage-graph theory). In the bipartite
degree–diameter problem, Haar graphs of cyclic groups appear at D = 3 (Feria-Purón–Miller–Pineda-Villavicencio,
Discrete Math. 313 (2013), the graphs Φ_m) [read], and dipole lifts over metacyclic groups are probably behind Loz's
values [inferred].

**The same construction, used for girth.** Haar graphs of SL(2, q), and graphs built from PSL(2, q) × Z_3, appear in
the cage literature (novelty check, claim 5, verdict "partial overlap"):

- G. Exoo, R. Jajcay, *On the girth of voltage graph lifts*, European J. Combin. 32 (2011) 554–562 [meta]. According to
  the dynamic cage survey (G. Exoo, R. Jajcay, Electron. J. Combin. Dynamic Survey DS16v3 (2013)) [read], the smallest
  known cubic graph of girth 30, on 1,143,408 = 2·|SL(2, 83)| vertices, is a voltage lift over SL(2, 83) of the θ-graph
  (two vertices joined by three parallel edges). That is a Haar graph H(SL(2, 83), S) with |S| = 3: the construction
  of this note, used there for girth.
- J. N. Bray, C. W. Parker, P. Rowley, *Cayley type graphs and cubic graphs of large girth*, Discrete Math. 214 (2000)
  113–121 [meta]. DS16 [read] lists their cubic graph of girth 27 on 285,852 vertices, built from PSL(2, 83) × Z_3. Its
  girth is odd, so it is neither bipartite nor a Haar graph; the overlap is the group PSL(2, q) × Z_n.

**Matrix groups elsewhere.**

- Lubotzky–Phillips–Sarnak, Combinatorica 8 (1988) 261–277 [meta]: their Ramanujan graphs include bipartite Cayley
  graphs of PGL(2, q). Their diameter is far from the log_{Δ−1} of the order that the records need: for the bipartite
  ones it is above (4/3)·log_{Δ−1} of the order, up to O(1) (N. T. Sardari, Combinatorica 39 (2019) 427–446,
  arXiv:1511.09340) [agent].
- G. Erskine, J. Tuite, *Large Cayley graphs of small diameter*, arXiv:1708.02425 [agent]: matrix groups over finite
  fields (a subgroup of SL(3, p)) for Cayley graphs in the degree–diameter problem for general graphs, diameters 3–5.
- Comellas's table of general graphs, entries of October 2026 [read]: (4,7) = 1,344, a regular voltage lift of a
  two-vertex base graph over SL(2, 7):C₂ (Yugeswardeenoo, 19 Oct 2026); and graphs of diameter 6 on generalized
  hexagons whose added edges are invariant under SL(2, q) acting regularly on the lines of a spread. These are not
  bipartite and not Haar graphs of SL(2, q) or PSL(2, q), but they lift over the same groups.
- Cayley graphs of SL(2, p) with random generators are expanders (Bourgain–Gamburd, Ann. of Math. 167 (2008)) and
  every generating set gives diameter O((log p)^c) (Helfgott, same volume) [read]. These results do not give the
  constant 1 in diam ≈ log_{Δ−1} |G| that the records need.

**Symmetric connection sets.** Requiring a connection set to be invariant under a group automorphism is an old device.
The Singer difference sets behind the D = 3 Moore graphs are fixed, up to translation, by the multiplier z ↦ qz of
order 3 (Hall's multiplier theorem) [classical]. We claim no novelty for the device.

**Elementary statements.** We claim no novelty for Lemma 1.2, Lemma 2.1, Theorem 2.4, Lemma 3.1 or Theorem 4.1; they
are routine and we include them so that the checks can be audited. Loz's thesis abstract says it "generalizes the
upper bound for abelian lifts of dipoles" [secondary], so a bound of the type of Theorem 4.3 is probably known in some
form; the version here, for every group through G/G′, was not part of the novelty check, and we claim no novelty for
it. For abelian groups (Corollary 4.4(i)) the count is the usual lattice-point count in an ℓ¹-ball behind upper
bounds for abelian Cayley graphs, which R. Dougherty and V. Faber relate to lattice coverings by octahedra (*The
degree-diameter problem for several varieties of Cayley graphs, I: the Abelian case*, arXiv:math/9412223)
[abstract]. Proposition 3.4(b) is the standard Lang-map argument (for fixed-point-free α it is the classical fact that
x ↦ x⁻¹α(x) is a bijection; see D. Gorenstein, *Finite Groups*, Ch. 10). Proposition 3.4(a) and Proposition 4.5 were
not part of the novelty check either; they are short and may well be folklore. Proposition 4.6 (§4.4) is of the same
kind as the cyclic multi-level products over generalized polygons in C. Delorme, Eur. J. Combin. 6 (1985) 291–302,
§3–4 [read], and the compound graphs of J. Gómez, M. A. Fiol, Ars Combin. 20-A (1985) 211–237 [meta]. A close recent
relative, named in the novelty check (claim 2), is R. Rajiv's compounds of polygon incidence graphs with point-to-line
matchings (Zenodo, 30 Sep 2026, https://doi.org/10.5281/zenodo.23052995; an unrefereed preprint; general graphs,
diameter n) [read]. We claim no novelty for Proposition 4.6.

### 6.2 What this note contributes

1. **The graphs of §5.** 34 cells at D = 8, 9, 10 where the lab's graph is larger than the table. All are Haar graphs
   except (3,8), which is a voltage lift. Most are Haar graphs of SL(2, q), PSL(2, q) or a product of two such groups,
   times a cyclic group, with 3·10⁴ to 4.2·10⁹ vertices. The type of construction is not the lab's: Haar graphs of
   SL(2, q) were used before for cubic graphs of large girth [Exoo–Jajcay], as was the group PSL(2, q) × Z_3
   [Bray–Parker–Rowley], and a voltage lift over SL(2, 7):C₂ is in the 2026 general-graph table (§6.1). For the
   bipartite degree–diameter problem, nothing was found in the sources searched by the novelty check: no paper or
   table entry using Haar graphs (bi-Cayley graphs) of SL(2, q), PSL(2, q) or PGL(2, q), alone or times a cyclic group,
   for large bipartite graphs of diameter 8, 9 or 10. Because Loz's constructions are unavailable, we cannot rule out
   that the small metacyclic cells ((5,8), (5,9), (4,10), (5,10)) use a method close to his.
2. **The search.** Simulated annealing over S with a bitset BFS evaluator (`research/frontier/haar_gen3.c`,
   `research/structured/haar_fast.c`), and orbit-closed S (Construction 3.2, `research/structured/haar_sym.c`) as a search
   device, with the measured effect of §3.5. Annealing and symmetric connection sets are standard devices, and we claim
   no novelty for them.
3. **The checks.** Independent checkers (§2.5), and Lean proofs for the graphs that are small enough (§5).
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
# for the 11 f = 0 files: solves alpha(s0) s0^-1 = tau and checks that T s0 is alpha-closed (reads the orbit_check logs)
python3 research/theorems/haar_d8_10/s0_check.py

# (3,8) is not a Haar graph: two distance profiles in each colour class
python3 research/theorems/haar_d8_10/lift38_profiles.py

# the numbers A(Delta, D) of Theorem 4.3
python3 research/theorems/haar_d8_10/abound.py

# Lean (needs elan; downloads Mathlib's cache); build one record module and its axiom check at a time
cd lean && lake exe cache get && lake build BipartiteDD.Haar.D7D8b.Record BipartiteDD.Haar.D7D8b.Axioms
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
s_{i_7} s_{i_6}⁻¹ s_{i_5} s_{i_4}⁻¹ s_{i_3} s_{i_2}⁻¹ s_{i_1} of seven letters with alternating signs. Equivalently
(Proposition 2.2), every element is the value of a reduced A-word of odd length ≤ 7; there are W(7,8) = 335,923 such
words for 47,880 elements. build_haar2.py, check_haar_indep.py and the coordinator's checks
confirm the covering (§5), and the graph is proved in Lean (`lean/BipartiteDD/Haar/`, §5).

The order is 14.25 % of the bipartite Moore bound 671,846; the table value is 80,940.

## Appendix B. Internal review

The note was refereed internally twice before this version, with brute-force checks on small groups
(`research/theorems/haar_d8_10/REFEREE_2026-10-25.md`, `REFEREE2_2026-10-25.md`). This version answers a third report
(`research/referee/haar-2026-10-25.md`, branch `claude/referee-haar-d8-10-jhckxf`) and the novelty check (§6); see the
response below.

## Referee response

Report: `research/referee/haar-2026-10-25.md` (branch `claude/referee-haar-d8-10-jhckxf`): 22 issues, none marked
ERROR. All 22 were applied; the points below are where this revision differs from the report's suggestion or adds to
it.

- **#1 (prior art).** Applied in §6.1 and §6.2. One correction to the suggested wording: the Bray–Parker–Rowley graph
  has girth 27, so it is neither bipartite nor a Haar graph. The note credits it for the group PSL(2, q) × Z_3, and
  credits Exoo–Jajcay for the Haar-graph construction itself.
- **#3 (values behind master).** The table keeps the values of commit `294fc94`, which the README still shows; §5 says
  so and names the two larger graphs recorded later in `research/RESULTS.md`. Which values go out is for the
  coordinator to decide; this revision adds no results. If the later values are adopted, the edits are the ones the
  report lists.
- **#4 (f = 0 orbit column).** Fixed by a check rather than by rewording. `s0_check.py` (its own arithmetic) solves
  α(s₀)s₀⁻¹ = τ in all 11 files. It finds |C_Q(g)| solutions in the matrix part of each, the same counts as the
  report, and verifies α(T s₀) = T s₀ with the stated cycle sizes for every solution.
- **#7 (§4.4).** Kept and proved (Proposition 4.6), instead of dropped.
- **#8 ((3,8) is not a Haar graph).** The distance profiles were recomputed with the lab's own lift builder
  (`lift38_profiles.py`); they agree with the report.
- **#19 (notation).** Renamed: the metacyclic Z_k (now Z_ℓ), the checker letters (now program codes bh2, ind, …), the
  ℓ of Proposition 3.3 (now L), the c of the (13,8) automorphism (now g), the matrix M of note 1 (now φ), Z_M in §4.4
  (now Z_n), the ε of §4.5 (now η) and the λ of §1.2 (removed). Kept: N for |G| next to N^b, A for the side and in
  A(Δ, D), m for the number of free orbits and the modulus of Z_m, and the c with which the orbit-check logs print τ
  (the text says so). None of these meanings meet inside one argument.
- **#20 (Dougherty–Faber).** Cited from the arXiv preprint (math/9412223), whose title and authors were checked. The
  journal details given in the report were not confirmed in this session, so they are not used.
