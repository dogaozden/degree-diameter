# Uniform families in the shape of the D = 8–10 Haar records: the LPS family, a 4/3 obstruction, and what a cyclic factor does

Doğa Özden's degree–diameter lab, with Claude Code (job `thm-haar-families`, 2026-10-27). Written for Gabriela
Araujo-Pardo and Ignacio López. Draft; corrections welcome.

**Labels.** Every statement carries one of three labels.

- **Theorem, Proposition, Lemma, Corollary**: complete proof in this note, or a cited result named in place (marked
  *cited*, with the source and how we know it: **[read]** primary source read, **[abstract]** abstract only,
  **[secondary]** known from a book, survey or citation).
- **Computer-checked**: a statement about finitely many explicit graphs, verified by programs that are named, with logs.
- **Heuristic**: a model, a measurement or an interpretation. Not used in any proof.

**The question.** The lab's records at D = 8, 9, 10 (`research/theorems/HAAR_D8_10.md` on branch
`claude/thm-haar-d8-10-sf7f0a`, cited below as [H]) are Haar graphs of SL(2, q) × Z_m or PSL(2, q) × Z_m whose
connection set S is closed under an automorphism of order 3, each found by computer search for one group. Can they be
turned into infinite families, with S given by one formula in q (and m) and a proved diameter?

**The answer, stated plainly.**

1. *There is an explicit infinite family of exactly this shape*, with m = 1: the connection sets of Lubotzky, Phillips
   and Sarnak (LPS). For every odd prime p and every prime q > p, the p + 1 LPS matrices in PGL(2, q) are permuted by
   conjugation with an element of order 3 of PSL(2, q), with cycle type 1+1+3+⋯+3 or 3+⋯+3: the cycle types that the
   orbit search used at Δ = 6, 8, 12, 14 (Theorem 2.6). For p ≡ 1 (mod 4) their diameter is at most 2 log_p n + O(1)
   (*cited*, LPS).
2. *This family provably cannot reach the records.* The vertex ψ(i) is at distance exactly the least even L with
   2p^{L/2} > q² (Theorem 3.2: lower bound for every odd p, equality for p ≡ 1 mod 4), so the diameter is at least
   (4/3) log_p n − 2 log_p 2 (Corollary 3.3, the bound of N. T. Sardari, here with a two-paragraph proof), and a member
   of diameter ≤ D has at most √2·p^{1−D/4} of the bipartite Moore bound (Corollary 3.4). Computed: the LPS graphs are
   2.5 to 19 times below the 2013 table at D = 8–10 (Appendix B), and at odd D the largest member is usually exactly
   the one that the vertex ψ(i) allows (8 of 13 cells; the next prime below in 3 more).
3. *A cyclic factor removes this obstruction in practice.* The obstruction survives every cover (Proposition 4.1), but
   it bounds q, not m. LPS × Z_m with labels chosen for each (q, m) reaches 99.4 % of the table at (6,10) and 98.9 % at
   (8,8) (Computer-checked 4.2), and with labels given by one formula in m (§4.3) the family has members **above the
   2013 table** at (8,8) (210,528 vertices against 201,480; q = 17, m = 43) and (8,9) (1,105,104 against 1,091,232;
   q = 23, m = 91), checked by two or three independent programs. They are below the lab's records there, and their
   diameters are computed, not proved.
4. *Other uniform formulas behave like one random draw.* Integer lifts, primitive-root and Dickson formulas, the conic
   model, torus orbits, and the records' own sets moved to other q (18 squad cards, §5) give an excess diam −
   log_{Δ−1}|G| no better than a single random draw at the same Δ (about 2.8–3.4 at Δ = 6–8; some kinds are worse),
   against about 2.0–2.3 for the records. Heuristically, the records' advantage is selection among millions of sets,
   which no single formula provides (§5–6).
5. *What would be needed is open.* A uniform family of record quality at fixed Δ would be an explicit family of
   bounded-degree graphs with diameter (1 + o(1)) log_{Δ−1} n. None is known; for the LPS graphs Sardari proved that it
   fails (§6).

No infinite family above the table is proved in this note; the members above the table in item 3 are single
computed graphs.

## Contents

0. Summary of statements
1. Setting, notation and projective coordinates
2. The LPS family has the records' shape
3. The 4/3 obstruction
4. Cyclic factors
5. Other uniform families (squad round 1)
6. Why no record-quality uniform family is in sight
7. Prior art
8. How to re-check

Appendix A. The squad rounds. Appendix B. The LPS family cell by cell.

---

## 0. Summary of statements

| # | statement | label |
|---|---|---|
| Prop. 1.1 | at fixed (Δ, D) only finitely many groups; for Q × Z_m with Q perfect, m ≤ A(Δ, D) | Proposition (from [H]) |
| Lemma 2.3 | ψ: H(Z) → M_2(F_q) is a ring homomorphism with kernel qH(Z); det ψ(α) = N(α); ψ(ᾱ) = adj ψ(α) | Lemma |
| Lemma 2.4 | for q > p the p + 1 matrices ψ(α), α ∈ S_p, are distinct in PGL(2, q), and ψ(S_p) is closed under inversion | Lemma |
| Lemma 2.5 | structure of the component Γ_{p,q}; diam Γ_{p,q} = ecc(I, A) | Lemma |
| Thm. 2.6 | conjugation by h = ψ(1+i+j+k), of order 3 in PSL(2, q), permutes ψ(S_p) with cycle type 1+1+3^{(p−1)/3} (p ≡ 1 mod 3), 3^{(p+1)/3} (p ≡ 2 mod 3), 1+3 (p = 3) | Theorem |
| Thm. 2.7 | Γ_{p,q} is connected and Ramanujan; diam ≤ 2 log_p n + O(1) | *cited* (LPS) |
| Lemma 3.1 | an even walk from (I, A) ends at ψ(β) with N(β) = p^L and β ≡ 1 mod 2H(Z) | Lemma |
| Thm. 3.2 | d((I,A), (ψ(i),A)) ≥ L₀ := min{L even : 2p^{L/2} > q²}, with equality if p ≡ 1 mod 4 | Theorem (equality uses a cited factorization) |
| Cor. 3.3 | diam Γ_{p,q} > (4/3) log_p n − 2 log_p 2 | Corollary |
| Cor. 3.4 | if diam Γ_{p,q} ≤ D then n < 2^{3/2} p^{3D/4} and n < √2·p^{1−D/4}·M^b(p+1, D) | Corollary |
| 3.5 | equality in Thm. 3.2 in all 251 cases p ∈ {3, 5, 7, 11, 13, 17, 19, 29}, p < q ≤ 160 (including p ≡ 3 mod 4); ecc − L₀ ∈ {0, 1, 2, 3} | Computer-checked |
| App. B | the LPS family cell by cell; at odd D its largest member is the one Thm. 3.2 allows in 8 of 13 cells | Computer-checked |
| Prop. 3.6 | the same lower bound in any definite quaternion order with an orthogonal unit γ | Proposition |
| Prop. 4.1 | the bound of Thm. 3.2 holds in every cover H(PGL(2,q) × K, S̃) of the LPS graph | Proposition |
| 4.2 | LPS × Z_m with searched labels: 99.4 % of the table at (6,10), 98.9 % at (8,8), 65 % at (14,8) | Computer-checked |
| 4.3 | LPS(7) × Z_m with labels by a formula: members above the 2013 table at (8,8) and (8,9) (below the lab's records) | Computer-checked |
| §5 | uniform formulas of six kinds: excess about that of one random draw | Computer-checked (scores), Heuristic (reading) |

---

## 1. Setting, notation and projective coordinates

### 1.1 Haar graphs

We use the conventions of [H] §1–2. For a finite group G and S ⊆ G with |S| = Δ, the Haar graph H(G, S) has vertex set
G × {A, B}, and (g, A) is adjacent to (sg, B) for every s ∈ S. It is bipartite and Δ-regular, the right translations
ρ_h(g, X) = (gh, X) are automorphisms acting regularly on each side ([H] Lemma 1.2), and its diameter is
max(ecc(e, A), ecc(e, B)) ([H] Cor. 2.3). A walk of length L from (e, A) uses letters t_1, …, t_L ∈ S and ends at
(w, A) or (w, B) with

$$w = \cdots t_4^{-1}\, t_3\, t_2^{-1}\, t_1 \qquad (\text{an } A\text{-word}),$$

and the walk backtracks exactly when two consecutive letters are equal ([H] Prop. 2.2). Lemma 3.1 of [H]: H(G, S) is
isomorphic to H(G, aψ(S)^{±1}b) for a, b ∈ G and ψ ∈ Aut(G); the map (g, A) ↦ (g, B), (h, B) ↦ (h, A) is an
isomorphism H(G, S) → H(G, S⁻¹).

Throughout, M^b(Δ, D) = 2 Σ_{j=0}^{D−1} (Δ − 1)^j is the bipartite Moore bound, and n denotes the number of vertices of
the graph at hand.

### 1.2 Projective coordinates

Let q be an odd prime. An element of PGL(2, q) is a nonsingular 2 × 2 matrix up to a nonzero scalar, that is, a point

$$[X] = [a : b : c : d] \in \mathrm{PG}(3, q), \qquad X = \begin{pmatrix} a & b \\ c & d\end{pmatrix},$$

not on the quadric 𝒬 : ad − bc = 0. The quadric 𝒬 is a hyperbolic quadric Q⁺(3, q) with (q + 1)² points, so PGL(2, q)
is the set of the (q + 1)(q² + 1) − (q + 1)² = q(q² − 1) points of PG(3, q) off 𝒬. Whether ad − bc is a square does not
depend on the representative, and PSL(2, q) is the set of the q(q² − 1)/2 points with ad − bc a nonzero square. For
M ∈ GL(2, q), left multiplication [X] ↦ [MX] is a collineation of PG(3, q) that fixes 𝒬 (det MX = det M det X).

So a Haar graph H(PGL(2, q), S) is the bipartite graph on two copies of PG(3, q) ∖ 𝒬 in which **the point [X] of the
first copy is joined to the points [MX], M ∈ S, of the second copy**; and the point [Y] of the second copy is joined to
the points [adj(M)·Y], M ∈ S, of the first, where adj [[a, b], [c, d]] = [[d, −b], [−c, a]] is the inverse up to a
scalar. These are the exact neighbourhoods of every vertex, once S is written down (§2, Example 2.8).

### 1.3 The records' shape

[H] Construction 3.2: S is closed under an automorphism α of order k, here k = 3, and splits into f fixed letters and
3-cycles; for G = Q × Z_m the automorphism is α(x, z) = (gxg⁻¹, rz) with g of order 3 modulo the centre of Q and r of
multiplicative order 3 mod m. The cycle types of the records are in [H] §5.1: 3+3 at (6,9), (6,10); 1+3+3 at Δ = 7;
1+1+3+3 at (8,8), (8,9), (8,10); 3+3+3 at (9,8), (9,9), (9,10); 3+3+3+3 at (12,9), (12,10); 1+1+3+3+3+3 at (14,9),
(14,10); and so on. Since |S| = f + 3c, f ≡ Δ (mod 3); every record with k = 3 uses the least such f ∈ {0, 1, 2}.

By a **uniform family** we mean, informally, one rule that produces S from q (and m) without a search for each q: a
formula, as for the Singer difference sets at D = 3. All the families below are uniform in this sense, except where a
search over labels is stated.

### 1.4 Where a uniform family can live

**Proposition 1.1.** (a) For fixed Δ ≥ 2 and D, only finitely many groups G admit S with |S| = Δ and
diam H(G, S) ≤ D. (b) If G = Q × Z_m with Q perfect (for example Q = SL(2, q) or PSL(2, q), q ≥ 4) and diam H(G, S) ≤ D,
then m ≤ A(Δ, D) = Θ(D^{Δ−1}) for fixed Δ.

*Proof.* (a) |G| ≤ M^b(Δ, D)/2 ([H] Thm. 4.1). (b) [H] Cor. 4.4(ii). ∎

So an infinite uniform family of the records' shape has Δ fixed and D → ∞ (and then q → ∞, since m grows at most
polynomially in D while |G| must grow exponentially), or D fixed and Δ → ∞. The LPS family below can be read in both
regimes (Corollary 3.4).

---

## 2. The LPS family has the records' shape

### 2.1 Definitions

Let H(Z) = {a₀ + a₁i + a₂j + a₃k : a_t ∈ Z} be the Lipschitz quaternions (i² = j² = k² = ijk = −1), with conjugate
ᾱ = a₀ − a₁i − a₂j − a₃k and norm N(α) = αᾱ = a₀² + a₁² + a₂² + a₃². N is multiplicative.

**Definition 2.1 (the LPS set).** For an odd prime p let S_p be the set of α ∈ H(Z) with N(α) = p and

- if p ≡ 1 (mod 4): a₀ > 0 odd, and a₁, a₂, a₃ even;
- if p ≡ 3 (mod 4): a₀ even, a₁, a₂, a₃ odd, and either a₀ > 0, or a₀ = 0 and a₁ > 0.

By Jacobi's four-square theorem |S_p| = p + 1 (*cited*: LPS, Combinatorica 8 (1988), §2, and G. Davidoff, P. Sarnak,
A. Valette, *Elementary Number Theory, Group Theory and Ramanujan Graphs*, LMS Student Texts 55 (2003), Ch. 2
[secondary]). If α ∈ S_p then ᾱ or −ᾱ is in S_p.

**Definition 2.2 (the splitting).** Let q be an odd prime, q ≠ p. Choose x, y ∈ F_q with x² + y² + 1 = 0 (they exist:
the sets {x²} and {−1 − y²} both have (q + 1)/2 elements, so they meet). Put

$$\psi(a_0 + a_1 i + a_2 j + a_3 k) = \begin{pmatrix} a_0 + a_1 x + a_3 y & -a_1 y + a_2 + a_3 x \\ -a_1 y - a_2 + a_3 x & a_0 - a_1 x - a_3 y\end{pmatrix} \bmod q .$$

**Lemma 2.3.** ψ: H(Z) → M_2(F_q) is a ring homomorphism with kernel qH(Z), and it is onto. det ψ(α) ≡ N(α), and
ψ(ᾱ) = adj ψ(α), so ψ(α)ψ(ᾱ) = N(α)·I.

*Proof.* ψ is additive and ψ(1) = I. Put M_i = ψ(i) = [[x, −y], [−y, −x]], M_j = ψ(j) = [[0, 1], [−1, 0]], M_k = ψ(k) =
[[y, x], [x, −y]]. Direct multiplication gives M_i² = (x² + y²)·I = −I, M_j² = −I, M_i·M_j = M_k and M_j·M_i = [[−y,
−x], [−x, y]] = −M_k. Since H(Z) is the ring generated over Z by i, j subject to i² = j² = −1 and ji = −ij (with k =
ij), the assignment i ↦ M_i, j ↦ M_j extends to a ring homomorphism, and it sends k to M_i·M_j = M_k; this is the
displayed formula. Its kernel contains qH(Z). If ψ(α) = 0, the diagonal gives a₀ + a₁x + a₃y = a₀ − a₁x − a₃y = 0, so a₀
= 0 and a₁x + a₃y = 0; the off-diagonal gives a₂ = 0 and a₃x − a₁y = 0. Then a₁(x² + y²) = x(a₁x + a₃y) − y(a₃x − a₁y) =
0, so a₁ = 0 (x² + y² = −1), and then a₃x = a₃y = 0 with (x, y) ≠ (0, 0), so a₃ = 0, all mod q. So the kernel is qH(Z),
and the induced map H(Z)/qH(Z) → M_2(F_q) is injective between sets of size q⁴, hence onto. The determinant of the
displayed matrix is (a₀ + a₁x + a₃y)(a₀ − a₁x − a₃y) − (a₂ + a₃x − a₁y)(−a₂ + a₃x − a₁y) = a₀² − (a₁x + a₃y)² + a₂² −
(a₃x − a₁y)² = a₀² + a₂² − (a₁² + a₃²)(x² + y²) = N(α). Finally adj ψ(α) has diagonal (a₀ − a₁x − a₃y, a₀ + a₁x + a₃y)
and off-diagonal entries −(−a₁y + a₂ + a₃x), −(−a₁y − a₂ + a₃x), which is ψ(a₀ − a₁i − a₂j − a₃k). ∎

**Lemma 2.4.** Let q > p. (a) If α, β ∈ H(Z) have N(α) = N(β) = p and ψ(α) = cψ(β) for some c ∈ F_q^×, then α = ±β.
(b) The p + 1 points [ψ(α)], α ∈ S_p, of PGL(2, q) are distinct, and the set they form is closed under inversion.

*Proof.* (a) γ = αβ̄ has N(γ) = p², and ψ(γ) = ψ(α)ψ(β̄) = cψ(β)ψ(β̄) = cp·I. By Lemma 2.3, γ − c̃p ∈ qH(Z) for an
integer c̃ ≡ c, so the coordinates γ₁, γ₂, γ₃ are divisible by q. They are at most √N(γ) = p < q in absolute value, so
they vanish: γ is an integer with γ² = p², γ = ±p. Then α = γβ̄⁻¹ = ±pβ/N(β) = ±β. (b) Distinct elements of S_p are
not negatives of each other (the sign conditions of Definition 2.1 fix the sign), so (a) gives distinctness. By
Lemma 2.3, [ψ(α)]⁻¹ = [adj ψ(α)] = [ψ(ᾱ)] = [ψ(±ᾱ)], and ±ᾱ ∈ S_p. ∎

**Definition 2.5'.** Γ_{p,q} is the connected component of (I, A) in H(PGL(2, q), ψ(S_p)).

**Lemma 2.5 (structure of Γ_{p,q}).** Let q > p and let c ∈ ψ(S_p).

(a) All of ψ(S_p) lies in one coset of PSL(2, q): in PSL(2, q) if p is a square mod q, in the other coset if not.
(b) The A-vertices of Γ_{p,q} form H₀ × {A} for a subgroup H₀ ≤ PSL(2, q), and its B-vertices cH₀ × {B}. The right
translations ρ_h, h ∈ H₀, map Γ_{p,q} to itself and act regularly on each side. When H₀ = PSL(2, q), Γ_{p,q} has
n = q(q² − 1) vertices.
(c) diam Γ_{p,q} = ecc(I, A) (computed in Γ_{p,q}).
(d) Γ_{p,q} ≅ H(PSL(2, q), c⁻¹ψ(S_p)) when it has q(q² − 1) vertices.

*Proof.* (a) det ψ(α) = p for all α (Lemma 2.3), and PSL(2, q) is the kernel of the homomorphism PGL(2, q) →
F_q^×/(F_q^×)² induced by the determinant. (b) A letter and its inverse both have determinant class [p], so an A-word of
length L has class [p]^L: it lies in PSL(2, q) for L even and in cPSL(2, q) for L odd. The set H₀ of the values of even
A-words (the A-side of Γ_{p,q}) is closed under products and contains I, so it is a subgroup of the finite group PSL(2,
q). Right translation ρ_h by h ∈ H₀ is an automorphism ([H] Lemma 1.2) mapping (I, A) to (h, A) ∈ Γ_{p,q}, so it maps
Γ_{p,q} to itself; {ρ_h : h ∈ H₀} acts regularly on the A-side H₀ × {A} and on the B-side cH₀ × {B}. When
Theorem 2.7 applies, H₀ = PSL(2, q). (c) By (b) and [H] Lemma 2.1 (with the group {ρ_h : h ∈ H₀}),
diam Γ_{p,q} = max(ecc(I, A), ecc(c, B)). Since ψ(S_p) is closed under inversion (Lemma 2.4), the side swap σ(g, A) =
(g, B), σ(g, B) = (g, A) is an automorphism of H(PGL(2, q), ψ(S_p)) ([H] Lemma 3.1(iv)); and ρ_c is one too. ρ_c∘σ maps
(I, A) to (c, B) and maps Γ_{p,q} onto the component of (c, B), which is Γ_{p,q} since (c, B) ~ (I, A). Hence ecc(c, B)
= ecc(I, A). (d) The map (g, A) ↦ (g, A), (h, B) ↦ (c⁻¹h, B) is the isomorphism H(G, S) → H(G, c⁻¹S) of [H] Lemma
3.1(i); restricted to Γ_{p,q} it lands in PSL(2, q) × {A, B}, and both graphs are Δ-regular with q(q² − 1) vertices. ∎

### 2.2 The order-3 symmetry

**Theorem 2.6.** Let p, q be odd primes, q > p, let ζ = 1 + i + j + k and h = ψ(ζ).

(a) h ∈ GL(2, q) has determinant 4, so [h] ∈ PSL(2, q), and [h] has order 3 in PGL(2, q).
(b) For every α ∈ H(Z), hψ(α)h⁻¹ = ψ(σ(α)), where σ(a₀ + a₁i + a₂j + a₃k) = a₀ + a₃i + a₁j + a₂k.
(c) Conjugation by h permutes the p + 1 points of ψ(S_p). Its fixed points are the [ψ(α)] with a₁ = a₂ = a₃, and its
cycle type is

| p | cycle type on ψ(S_p) | Δ = p + 1 | records with this cycle type ([H] §5.1) |
|---|---|---|---|
| p = 3 | 1 + 3 | 4 | none (Δ = 4 records are metacyclic) |
| p ≡ 1 (mod 3) | 1 + 1 + 3^{(p−1)/3} | 8 (p = 7), 14 (p = 13), 20, 32, 38, … | (8,8), (8,9), (8,10); (14,9), (14,10) |
| p ≡ 2 (mod 3) | 3^{(p+1)/3} | 6 (p = 5), 12 (p = 11), 18, 24, 30, … | (6,9), (6,10); (12,9), (12,10) |

So the LPS Haar graph is an orbit-closed Haar graph in the sense of [H] Construction 3.2, with α = conjugation by an
element of order 3 of PSL(2, q) and m = 1, and with the same cycle type as the records at Δ = 6, 8, 12 and 14.

*Proof.* (a) N(ζ) = 4, so det h = 4 = 2², a nonzero square (q odd). Write v = i + j + k, so v² = −3 and ζ = 1 + v;
then ζ² = 1 + 2v + v² = −2 + 2v and ζ³ = (−2 + 2v)(1 + v) = −2 − 2v + 2v + 2v² = −8. So h³ = −8I is a scalar. And h
is not a scalar: ψ(ζ) − c̃I = ψ(ζ − c̃) would vanish only if ζ − c̃ ∈ qH(Z) (Lemma 2.3), but the i-coordinate of
ζ − c̃ is 1. So [h] has order 3.

(b) We compute ζiζ̄. First ζi = i + i² + ji + ki = −1 + i + j − k. Then
(−1 + i + j − k)(1 − i − j − k) = (−1 + i + j + k) + (i + 1 + j − k) + (j + k + 1 − i) + (−k + j − i − 1) = 4j,
using ij = k, ik = −j, ji = −k, jk = i, ki = j, kj = −i. So ζiζ̄ = 4j, that is, ζiζ⁻¹ = j. Applying the ring
automorphism of H(Z) that permutes i → j → k → i (it preserves the relations and fixes ζ), we get ζjζ⁻¹ = k and
ζkζ⁻¹ = i. Hence ζαζ⁻¹ = σ(α), and ζαζ̄ = 4σ(α). Applying ψ (Lemma 2.3): hψ(α)·adj(h) = 4ψ(σ(α)), and
adj(h) = det(h)·h⁻¹ = 4h⁻¹.

(c) σ preserves the norm, the coordinate a₀ and the parity pattern of (a₁, a₂, a₃). If p ≡ 1 (mod 4), σ(S_p) = S_p. If
p ≡ 3 (mod 4), σ(α) satisfies Definition 2.1 except possibly the sign rule when a₀ = 0, so σ(α) or −σ(α) lies in S_p,
and ψ(−β) = −ψ(β) is the same point of PGL(2, q). So conjugation by h permutes ψ(S_p). By Lemma 2.4(a), [ψ(σα)] = [ψ(α)]
iff σ(α) = ±α. The case σ(α) = −α forces a₀ = 0 and (a₃, a₁, a₂) = (−a₁, −a₂, −a₃), so a₁ = −a₃ = a₂ = −a₁, so α = 0,
impossible. So the fixed points are the α ∈ S_p with a₁ = a₂ = a₃ =: a, i.e. with a₀² + 3a² = p.

- If p ≡ 2 (mod 3), a₀² + 3a² ≡ a₀² ∈ {0, 1} (mod 3), so there is no fixed point.
- If p ≡ 1 (mod 3), the equation a₀² + 3a² = p has exactly four integer solutions (±a₀, ±a), with a₀, a ≠ 0 (Fermat;
  for a prime p ≡ 1 mod 3 the representation p = x² + 3y² with x, y > 0 is unique; *cited*: D. A. Cox, *Primes of the
  form x² + ny²*, Wiley 1989, §1 [secondary]). If p ≡ 1 (mod 4) then a₀ is odd and a even (odd + odd ≡ 0 and
  even + 3·odd ≡ 3 mod 4), so exactly the two solutions with a₀ > 0, namely a₀ + a(i + j + k) with a = ±|a|, are in
  S_p. If p ≡ 3 (mod 4) then a₀ is even and a odd, a₀ ≠ 0 (p ≠ 3a²), and again exactly the two with a₀ > 0 are in S_p.
  So there are two fixed points.
- If p = 3: a₀ = 0, a = ±1, and of ±(i + j + k) only i + j + k is in S_3. One fixed point.

Since [h] has order 3, every other point lies in a 3-cycle, which gives the cycle types. ∎

**Theorem 2.7 (*cited*: Lubotzky–Phillips–Sarnak, Combinatorica 8 (1988) 261–277 [secondary for the constants];
Davidoff–Sarnak–Valette (2003), Ch. 4 [secondary]).** Let p ≡ 1 (mod 4) and let q > p be an odd prime. Then
Γ_{p,q} has q(q² − 1) vertices (that is, the LPS Cayley graph X^{p,q} is connected), every eigenvalue of its adjacency
matrix other than ±(p + 1) has absolute value at most 2√p (Ramanujan), and diam Γ_{p,q} ≤ 2 log_p n + O(1), with an
explicit constant given by LPS.

*Remark.* Γ_{p,q} is X^{p,q} itself when p is not a square mod q (X^{p,q} is then a bipartite Cayley graph of
PGL(2, q), and a bipartite Cayley graph whose connection set lies in the non-trivial coset of an index-2 subgroup is a
Haar graph of that subgroup, Lemma 2.5(d)); it is the bipartite double cover of X^{p,q} when p is a square mod q.
*Computer-checked*: Γ_{p,q} has q(q² − 1) vertices for p ∈ {3, 5, 7, 11, 13} and every prime p < q ≤ 160 (logs
`haar_families/scan/lps_p*.txt`, column "vertices"), including p ≡ 3 (mod 4), which Theorem 2.7 as cited does not cover.

### 2.3 The family written out at Δ = 6

**Example 2.8 (p = 5).** S_5 = {1 ± 2i, 1 ± 2j, 1 ± 2k}. With x² + y² = −1 in F_q, the six matrices are

$$\psi(1 \pm 2i) = \begin{pmatrix} 1 \pm 2x & \mp 2y \\ \mp 2y & 1 \mp 2x\end{pmatrix},\quad
\psi(1 \pm 2j) = \begin{pmatrix} 1 & \pm 2 \\ \mp 2 & 1\end{pmatrix},\quad
\psi(1 \pm 2k) = \begin{pmatrix} 1 \pm 2y & \pm 2x \\ \pm 2x & 1 \mp 2y\end{pmatrix},$$

and conjugation by h = ψ(1 + i + j + k) = [[1 + x + y, 1 + x − y], [−1 + x − y, 1 − x − y]] cycles
1 + 2i → 1 + 2j → 1 + 2k → 1 + 2i and the same with −2: cycle type 3 + 3. In the coordinates of §1.2, **the point
[a : b : c : d] of the first copy of PSL(2, q) is joined to the six points**

$$[\,(1 \pm 2x)a \mp 2yc : (1 \pm 2x)b \mp 2yd : \mp 2ya + (1 \mp 2x)c : \mp 2yb + (1 \mp 2x)d\,],$$
$$[\,a \pm 2c : b \pm 2d : c \mp 2a : d \mp 2b\,],\qquad
[\,(1 \pm 2y)a \pm 2xc : (1 \pm 2y)b \pm 2xd : \pm 2xa + (1 \mp 2y)c : \pm 2xb + (1 \mp 2y)d\,]$$

of the second copy; and the point [a : b : c : d] of the second copy is joined to the same six expressions, read as
points of the first copy (by Lemma 2.3, adj ψ(α) = ψ(ᾱ), and S̄_5 = S_5, so the six adjugates are the same six matrices
up to scalars). For q = 13, with (x, y) = (0, 5) (the first solution of x² + y² + 1 ≡ 0 found by the programs), the
component of the first copy's identity is a 6-regular bipartite graph on 2184 vertices of diameter 7 (computer-checked
by `lps_haar`, `haar_ecc` and the all-pairs BFS `apsp.c`, §8).

---

## 3. The 4/3 obstruction

**Lemma 3.1 (walk values).** Let p, q be odd primes, q > p. A walk of even length L in H(PGL(2, q), ψ(S_p)) from (I, A)
ends at a vertex ([ψ(β)], A) with β ∈ H(Z), N(β) = p^L and β ≡ 1 (mod 2H(Z)); in particular the real coordinate b₀ of
β is odd.

*Proof.* The walk with letters ψ(α_1), …, ψ(α_L) ends at s_L⁻¹s_{L−1}⋯s_2⁻¹s_1 with s_t = ψ(α_t), and
[ψ(α)⁻¹] = [ψ(ᾱ)] (Lemma 2.3). So it ends at [ψ(β)] with β = ᾱ_L α_{L−1} ⋯ ᾱ_2 α_1, and N(β) = p^L. Reduce mod 2: in
H(Z)/2H(Z) we have −1 = 1, so i, j, k commute there. If p ≡ 1 (mod 4), every α_t and ᾱ_t is ≡ 1 (mod 2H(Z)), so β ≡ 1.
If p ≡ 3 (mod 4), every α_t and ᾱ_t is ≡ v := i + j + k, and v² = −3 ≡ 1, so β ≡ v^L = 1 since L is even. ∎

**Theorem 3.2 (distance to ψ(i)).** Let p, q be odd primes with q > p, and let L₀ be the least even integer L ≥ 0 with
2p^{L/2} > q². In Γ_{p,q}:

(a) d((I, A), ([ψ(i)], A)) ≥ L₀, and the same holds for ψ(j) and ψ(k);
(b) if p ≡ 1 (mod 4), equality holds.

Note that det ψ(i) = N(i) = 1, so [ψ(i)] ∈ PSL(2, q) for every q.

*Proof.* (a) A path from (I, A) to ([ψ(i)], A) has even length L (the graph is bipartite). By Lemma 3.1 there is β with
N(β) = p^L, b₀ odd and [ψ(β)] = [ψ(i)], i.e. ψ(β) = cψ(i) with c ∈ F_q^×. By Lemma 2.3, β − c̃i ∈ qH(Z), so
q | b₀, b₂, b₃. Put P = p^{L/2}, an integer. Since b₀ is odd, b₀ ≠ 0, so b₀² ≥ q², and then
b₁² = P² − b₀² − b₂² − b₃² ≤ P² − q², so |b₁| < P. Also q² divides b₀² + b₂² + b₃² = P² − b₁² = (P − b₁)(P + b₁). The
prime q does not divide P (q ≠ p), so q cannot divide both factors (it would divide their sum 2P). Hence q² divides
P − εb₁ for some ε ∈ {1, −1}. Since |b₁| < P, 0 < P − εb₁ < 2P, so q² ≤ P − εb₁ < 2P. That is 2p^{L/2} > q², and
L ≥ L₀. For ψ(j) and ψ(k): conjugation by h fixes (I, A), is an automorphism of H(PGL(2, q), ψ(S_p)) (Theorem 2.6 and
[H] Prop. 3.3(a)), and maps [ψ(i)] to [ψ(j)] to [ψ(k)] (Theorem 2.6(b)), so the three distances are equal.

(b) Let L = L₀, P = p^{L/2}, and put n₁ = 2P − q² > 0. Here P ≡ 1 (mod 4) (p ≡ 1 mod 4), so 2P ≡ 2 (mod 8), and
q² ≡ 1 (mod 8), so n₁ ≡ 1 (mod 8). By the Gauss–Legendre three-square theorem (*cited*; n is a sum of three squares
unless n = 4^a(8b + 7)), n₁ = u² + v² + w² with integers u, v, w; since n₁ ≡ 1 (mod 4), exactly one of them is odd, and
we name it u. Put

$$\beta = qu + (P - q^2)\,i + qv\,j + qw\,k .$$

Then N(β) = q²(u² + v² + w²) + (P − q²)² = q²(2P − q²) + P² − 2Pq² + q⁴ = P² = p^L; b₀ = qu is odd, b₁ = P − q² is even,
and b₂ = qv, b₃ = qw are even; so β ≡ 1 (mod 2H(Z)). And β ≡ P·i (mod qH(Z)), so [ψ(β)] = [Pψ(i)] = [ψ(i)]. By the
LPS factorization theorem (*cited*: LPS 1988 §3; Davidoff–Sarnak–Valette (2003), Ch. 2, the unique factorization of
quaternions β ≡ 1 mod 2 of norm p^L [secondary]), β = ±p^r α_1α_2⋯α_{L−2r} with α_t ∈ S_p and r ≥ 0. Since
[ψ(±p^r γ)] = [ψ(γ)], we get [ψ(i)] = [ψ(α_1⋯α_{L'})] with L' = L − 2r even. Choose the letters
s_1 = ψ(α_{L'}), s_2 = ψ(ᾱ_{L'−1}) (so [s_2⁻¹] = [ψ(α_{L'−1})]), s_3 = ψ(α_{L'−2}), s_4 = ψ(ᾱ_{L'−3}), …; they lie in
ψ(S_p) up to sign (Lemma 2.4(b)), and the A-word s_{L'}⁻¹ ⋯ s_2⁻¹s_1 has value [ψ(α_1⋯α_{L'})]. So there is a walk of
length L' ≤ L₀ from (I, A) to ([ψ(i)], A). With (a), the distance is L₀. ∎

**Corollary 3.3.** For odd primes q > p, with n = q(q² − 1) ≥ |V(Γ_{p,q})|:

$$\operatorname{diam}\Gamma_{p,q} \;\ge\; L_0 \;\ge\; 4\log_p q - 2\log_p 2 \;>\; \tfrac43 \log_p n - 2\log_p 2 .$$

*Proof.* 2p^{L₀/2} > q² gives L₀ > 2 log_p(q²/2) = 4 log_p q − 2 log_p 2, and n < q³. ∎

**Corollary 3.4 (a vanishing fraction of the Moore bound).** Let p be an odd prime, D ≥ 2, and q > p a prime with
diam Γ_{p,q} ≤ D. Then q² < 2p^{⌊D/2⌋}, the number of vertices satisfies

$$n \le q(q^2-1) < 2^{3/2}\, p^{\frac32\lfloor D/2\rfloor} \le 2^{3/2} p^{3D/4},$$

and n < √2·p^{1−D/4}·M^b(p + 1, D). In particular, along the LPS family the fraction of the Moore bound tends to 0
both for fixed p and D → ∞ and for fixed D ≥ 5 and p → ∞.

*Proof.* L₀ ≤ diam ≤ D and L₀ is even, so L₀ ≤ 2⌊D/2⌋ and 2p^{⌊D/2⌋} ≥ 2p^{L₀/2} > q². Then n < q³ < (2p^{⌊D/2⌋})^{3/2}.
Finally M^b(p + 1, D) = 2Σ_{j<D} p^j > 2p^{D−1}, so n/M^b < 2^{3/2}p^{3D/4}/(2p^{D−1}) = √2·p^{1−D/4}. ∎

For comparison: at D = 8 the bound is √2/p (28 % for p = 5), and the LPS graphs actually reach 1–6 % (Appendix B);
the lab's records at D = 8 are at 8–22 %, and the D = 8 table values with Δ ≥ 10 (Gómez's compounds of generalized
hexagons) at about 10 % ([H] §5, §6). In the regime D fixed, Δ → ∞, Delorme's constructions from generalized polygons
have lim inf n·Δ^{1−D} > 0 for every D (C. Delorme, J. Graph Theory 9 (1985) 325–334 [abstract]), so arithmetic Haar
families lose to them by a factor p^{D/4−1}.

**Computer-checked 3.5.** For p ∈ {3, 5, 7, 11, 13, 17, 19, 29} and every prime q with p < q ≤ 160, the distance from
(I, A) to ([ψ(i)], A), ([ψ(j)], A) and ([ψ(k)], A), computed by breadth-first search (`lps_haar.c`), equals L₀: no
exception in 251 cases (log `haar_families/recheck_thmB.log`). This includes p ≡ 3 (mod 4), where equality is not proved
here. The eccentricity of (I, A) exceeds L₀ by 0, 1, 2 or 3 (in 76, 151, 22 and 2 of the 251 cases). So in this range
the special vertex ψ(i) accounts for the diameter up to at most 3, and at odd D it is usually what limits the family
(Appendix B). The construction in the proof of Theorem 3.2(b) (u, v, w, and β with N(β) = p^{L₀}, β ≡ 1 mod 2 and [ψ(β)]
= [ψ(i)]) was also checked directly for p ∈ {5, 13, 17, 29, 37} and all primes p < q < 1000 (802 cases,
`haar_families/check_thmB_construction.py`). An independent re-implementation by squad card c8 (its own quaternion
arithmetic and BFS; `research/squads/thmfam-r1/c8/`) confirmed Theorem 2.6(c) for all 137 pairs with 7 ≤ q ≤ 61 and
Theorem 3.2 in 41 cases with q ≡ 1 (mod 4), and its all-pairs BFS (`apsp.c`) agreed with `haar_ecc` on six LPS graphs.
(The squad card also found a bug in the first version of `lps_haar.c`, which mixed the distances of the two sides; the
logs above are from the corrected version.)

**Proposition 3.6 (the same obstruction in other definite quaternion orders).** Let 𝒪 be a Z-order in a definite
quaternion algebra over Q, with norm form N, and suppose 𝒪 = Zγ ⊕ 𝒪′ with N(aγ + β′) = a² + N(β′) for a ∈ Z,
β′ ∈ 𝒪′ (an orthogonal unit γ, N(γ) = 1). Let ψ: 𝒪 → M_2(F_q) be a ring homomorphism with kernel q𝒪 (q an odd prime,
q ∤ p), let S ⊆ 𝒪 be a set of elements of norm p closed under conjugation up to sign, and suppose that no product of
an even number L ≥ 2 of elements of S lies in Zγ. Then in H(PGL(2, q), ψ(S)), every walk of even length L from (I, A)
to ([ψ(γ)], A) has 2p^{L/2} > q².

*Proof.* As in Lemma 3.1 the walk ends at [ψ(β)] with β a product of L elements of S (conjugates included), so
N(β) = p^L; [ψ(β)] = [ψ(γ)] gives β = bγ + qβ″ with b ∈ Z, β″ ∈ 𝒪′ (the kernel of ψ is q𝒪 and 𝒪 = Zγ ⊕ 𝒪′), and
β″ ≠ 0 by hypothesis. Then P² = b² + q²N(β″) with P = p^{L/2} and N(β″) ≥ 1, and the second half of the proof of
Theorem 3.2(a) applies verbatim (q ∤ P, q² | P − εb, 0 < P − εb < 2P). ∎

For the Hamilton order, γ = i, 𝒪′ = Z + Zj + Zk, and the hypothesis is Lemma 3.1 (every even product is ≡ 1 mod 2,
while elements of Zi have even real part). *Computer-checked* (squad card c9 of round 2,
`research/squads/thmfam-r2/c9/`): in the order Z⟨1, i, j, ij⟩ with i² = −1, j² = −3 (norm a₀² + a₁² + 3a₂² + 3a₃²),
with S a set of p + 1 classes of elements of norm p modulo the units ±1, ±i, for p ∈ {5, 7, 11} and q ≤ 97, the
distance from (I, A) to ([ψ(i)], A) equals the least even L with 2p^{L/2} > q² in 65 of 66 cases (in the remaining
case, p = 5, q = 61, it is 12 instead of 10), and ψ(i) is at maximal distance for p = 5, q ∈ {61, 83, 97}. So the
obstruction is a property of definite quaternion arithmetic with a unit orthogonal to the rest, not of Hamilton's
order. (The card did not check the hypothesis "no even product in Zi" for its set; the lower bound it measured holds in
all 66 cases.)

**Remark 3.7 (prior art).** The lower bound (4/3) log_p n + O(1) for the diameter of the bipartite LPS graphs is due to
N. T. Sardari, *Diameter of Ramanujan graphs and random Cayley graphs*, Combinatorica 39 (2019) 427–446,
arXiv:1511.09340 [abstract]; his abstract also states that almost all pairs of vertices of a Ramanujan graph are at
distance at most (1 + ε) log_{p} n, and reports numerics in which LPS diameters grow like (4/3) log and those of random
Cayley graphs like log. We did not read his proof; the argument above is short and may be his. The exact value in
Theorem 3.2(b) follows from the same arithmetic and the LPS factorization; we did not check whether it is stated
there. That the LPS sets are permuted by the Hurwitz unit (1 + i + j + k)/2 is classical; we found no source that
compares their cycle types with orbit-searched connection sets, and claim nothing more than the observation.

---

## 4. Cyclic factors

**Proposition 4.1.** Let K be a finite group, κ: S_p → K any map, and S̃ = {(ψ(α), κ(α)) : α ∈ S_p} ⊆ PGL(2, q) × K.
Then for every k ∈ K, the distance in H(PGL(2, q) × K, S̃) from (I, e_K, A) to ([ψ(i)], k, A) is at least L₀. Hence if
the component of (I, e_K, A) has diameter ≤ D and contains ([ψ(i)], k, A) for some k, then q² < 2p^{⌊D/2⌋}.

*Proof.* The projection (g, k, X) ↦ (g, X) maps every edge {(g, k, A), (ψ(α)g, κ(α)k, B)} to the edge
{(g, A), (ψ(α)g, B)}, so it maps walks to walks of the same length and does not decrease distances. Apply
Theorem 3.2(a). ∎

So a cyclic factor cannot help at the vertex ψ(i) with a fixed q; what it changes is that m is free. The order is
q(q² − 1)·m, the obstruction bounds only q, and the counting bound ([H] Thm. 4.1) allows m up to about
p^{D−1}/q³. Whether the cyclic part can be filled efficiently is a computational question:

**Computer-checked 4.2 (squad cards c6, c7).** Let r have order 3 mod m. Labels α ↦ z(α) ∈ Z_m that are equivariant for
the order-3 symmetry (z(σα) = r·z(α); fixed letters get 0; one 3-cycle gets (1, r, r²) without loss of generality, the
others (t, rt, r²t)) make H(PGL(2, q) × Z_m, S̃) orbit-closed with α(x, z) = (hxh⁻¹, rz), exactly the records' shape.
Searching t for each (q, m), the squads found:

| cell | best LPS × Z_m (q, m) | vertices | of table | lab record | LPS alone (Appendix B) |
|---|---|---:|---:|---:|---:|
| (6,8) | (13, 13) | 28,392 | 95.3 % | 31,680 | 12,144 |
| (6,9) | (13, 43) | 93,912 | 80.0 % | 127,296 | 24,360 |
| (6,10) | (23, 37) | 449,328 | 99.4 % | 524,160 | 148,824 |
| (8,8) | (11, 151) | 199,320 | 98.9 % | 239,904 | 29,760 |
| (8,9) | (23, 73) | 886,512 | 81.2 % | 1,341,600 | 300,696 |
| (14,8) | (29, 379) | 9,232,440 | 65.1 % | none (the lab does not beat this cell) | 1,294,920 |

Every entry was re-checked by the director with `haar_ecc` (two-source BFS on the component, from the cards' generators:
`research/squads/thmfam-r1/c6/gen_c6.py`, `research/squads/thmfam-r1/c7/c7lib.py`), and (6,10) and (8,8) also with
`verify_cover.py` (independent Python arithmetic; eccentricities 10, 10 and 8, 8). These graphs are below the lab's
records and below the table, and their labels were searched for each (q, m): they are not a uniform family. They show
that the cyclic factor removes most of the 4/3 loss in practice: at (6,10) the cover is 3.0 times the LPS graph alone.

### 4.3 A label rule: a formula in q and m that beats the 2013 table at (8,8) and (8,9)

Fix p = 7, so Δ = 8 and S_7 = {2 ± (i + j + k)} ∪ C₁ ∪ C₂ with the two 3-cycles of σ

C₁ = {2 − i − j + k, 2 + i − j − k, 2 − i + j − k},  C₂ = {2 − i + j + k, 2 + i − j + k, 2 + i + j − k}

(in the order α, σα, σ²α). For m whose prime factors are all ≡ 1 (mod 3), let r be a root of r² + r + 1 ≡ 0 (mod m)
and give the labels

z(2 ± (i + j + k)) = 0,  z(C₁) = (1, r, r²),  z(C₂) = (t, tr, tr²)

with t a fixed integer (t = 2 below), or a fixed function of m (t = m − 2). This defines S̃(q, m) ⊆ PGL(2, q) × Z_m
by one formula in q and m: no search. It is closed under the automorphism (x, z) ↦ (hxh⁻¹, rz) of order 3, the
records' shape. The vertex (X, z, A), X ∈ PSL(2, q), is adjacent to the eight vertices (ψ(α)X, z + z(α), B), α ∈ S_7.

**Computer-checked 4.3 (squad card c2 of round 2, re-checked by the director).** Over the grid q ∈ {11, 13, 17, 19,
23} × m ∈ {7, 13, 19, 31, 37, 43, 61, 49, 91} (45 cells, all components full), the rules t = 2, t = 3, t = 5, t = m − 2
and others have mean excess 2.63–2.66, against 2.72–2.77 for one random t per cell (two seeds). Two members of the
family are above the 2013 table:

| cell | (q, m), rule, r | vertices | 2013 table | lab record | checks |
|---|---|---:|---:|---:|---|
| (8,8) | (17, 43), t = 2, r = 36 | **210,528** | 201,480 (+4.5 %) | 239,904 | `haar_ecc`, `verify_cover.py`, all-pairs `apsp.c` |
| (8,9) | (23, 91), t = m − 2 = 89, r = 9 | **1,105,104** | 1,091,232 (+1.3 %) | 1,341,600 | `haar_ecc`, `verify_cover.py` |

(generators: `haar_families/covers/d8D8_lps7_q17_m43.gens`, `d8D9_lps7_q23_m91.gens`; log `covers/recheck.log`.)
Both are below the lab's records at these cells ([H] §5), so they are not new records; and (q, m) is the best cell of
the grid, chosen after the fact. What they show is that a member of a uniform arithmetic family of the records' exact
shape (k = 3, cycle type 1 + 1 + 3 + 3, an inner automorphism of order 3 times a scaling of Z_m) is above the 2013 table
at D = 8 and 9, while the same family without the cyclic factor is 6.8 and 3.6 times below it (Appendix B). We do not
have a proof of the diameter of any member: the proofs of §3 give lower bounds only.

**Label rules elsewhere (round 2).** For p = 5 the best fixed rule (t = 3) has mean excess 2.86 over 45 cells, against
2.93–3.09 for one random t per cell (card c1); a nonlinear rule z(α) = Σ_k (a_k mod 3)·r^{k−1} gives 2.82 over 24 cells
(card c11); over 35 cells, one random equivariant labelling gives 2.97 and the best t per cell 2.71 (card c10,
exhaustive over t and both roots r). For p = 7, one random equivariant labelling gives 2.68 (card c10). For p = 11, the
best of 10 rules ties with random labels (2.53 against 2.56 over 4 × 8 cells; card c3). So a fixed rule recovers about
half of the gain that a search over t gives at p = 5, and little or nothing at p = 7 and 11. For Δ = 4 (p = 3), covers
with labels searched exhaustively reach 66 % of the table at (4,8) and 88 % at (4,9) (card c6), so the cells (4,8),
(4,9), which the lab does not beat, stay unbeaten. For Δ = 12 the best cover found reaches 51 % of the table at (12,9)
and none of diameter 8 improves on plain LPS (card c7); for Δ = 14 the best is the 65 % graph at (14,8) of §4.2.

---

## 5. Other uniform families (squad round 1)

**Score.** For a family S(q) and the primes 23 ≤ q ≤ 113, the *excess* is diam − log_{Δ−1}|G| with |G| = one side of
the graph, averaged over q (`haar_families/family_score.py`, which runs `haar_ecc`). Lower is better. A uniform family
gets one S per q, so it should be compared with *one* random orbit-closed draw per q, not with the records, which are
the best of millions of evaluations for one (q, m).

**Computer-checked 5.1 (mean excess, 22 primes 23 ≤ q ≤ 113, group PSL(2, q) unless stated; from
`research/squads/thmfam-r1/scoreboard.jsonl` and the cards' folders).** Baselines first (card c13: 8 seeds each, mean
± standard deviation over seeds):

| one random draw per q | Δ = 6 | Δ = 7 | Δ = 8 |
|---|---:|---:|---:|
| random S, no symmetry, PSL | 3.20 ± 0.05 | 2.95 ± 0.05 | 2.95 ± 0.05 |
| random S, no symmetry, SL | 3.05 ± 0.02 | 2.89 ± 0.03 | 2.76 ± 0.03 |
| random orbit-closed S (k = 3), PSL | 3.31 ± 0.11 | 3.04 ± 0.10 | 3.28 ± 0.08 |
| random orbit-closed S (k = 3), SL | 3.34 ± 0.11 | 3.09 ± 0.09 | 3.14 ± 0.09 |

(Orbit-closed sets with Δ = 7, 8 contain I, and I and w, as in the records; the unconstrained sets are Δ distinct
random elements.) The spread of the excess over q is 0.1–0.4 per prime. So a single orbit-closed draw is slightly
*worse* than a single unconstrained draw (by 0.1–0.4); the orbit search wins
because it makes the search space smaller and the misses come in clumps ([H] §3.5), not because orbit-closed sets are
better one by one. The families:

| family (one S per q, no search per q) | Δ | mean excess | card |
|---|---|---:|---|
| LPS, p = 5 (component in PGL(2, q)) | 6 | 4.00 | director |
| integer lifts, O(X) ∪ O(Y), X, Y ∈ SL(2, Z), entries ≤ 3 (best of 206) | 6 | 3.36 | c1 |
| Dickson / trace / power formulas (best of 15) | 6 | 3.13 | c11 |
| integer lifts, {I} ∪ O(X) ∪ O(Y) (best of 1212; mean of the top 10: 3.35) | 7 | 3.10 | c2 |
| primitive-root formulas, e.g. X = [[g, 1], [0, g⁻¹]], Y = [[1/2, g], [g, 2(1 + g²)]] (best of 16) | 7 | 2.96 | c10 |
| integer lifts × Z_13, equivariant labels (best of about 500 screened) | 7 | 3.12 | c4 |
| integer lifts, two fixed letters + two orbits (all 234 with entries ≤ 2) | 8 | 3.84 | c3 |
| Dickson / trace / power formulas (best of 15) | 8 | 3.16 | c11 |
| conic model: Cayley transforms of integer matrices (best of 8) | 8 | 3.34 | c16 |
| integer lifts, one fixed letter + three orbits (all 858 with entries ≤ 2) | 10 | 3.40 (random orbit-closed: 2.76) | c3 |
| single orbits of order 6 (best uniform x, y) | 12 | 2.73 (random, k = 3: 2.55–2.64) | c15 |
| LPS + one extra α-orbit (repair) | 9 | 3.24 on 7 primes (random: 2.72–2.86) | c18 |
| the records' own sets, lifted to SL(2, Z) and used at the other 21 primes | 6, 7 | 2.87–3.24 (at their own q: 1.99–2.13) | c5 |
| SL(2, q) × Z_m, m ≈ q, integer letters with equivariant labels (10 primes 23–61) | 6 | 3.38 (same letters, m = 1: 3.60) | c17 |
| the lab's records (one (q, m) each, annealed) | 6–16 | about 2.0–2.3 | [H] |

Torus-orbit families with Δ growing like q (card c12: S = {I} ∪ T-conjugates of x for a torus T of PSL(2, q)) have
diameter 5 to 7 for 31 ≤ q ≤ 61 and reach at most 1.8 % of the Moore bound at their diameter; no family of diameter
≤ 4 appeared. The excess of LPS grows with log_5|G| with slope 0.41 (card c14, 38 primes 23 ≤ q ≤ 199; Corollary 3.3
predicts 1/3), that of random orbit-closed draws with slope −0.04.

**Heuristic 5.2 (reading of 5.1).**

1. No formula family beats one random draw at the same Δ by more than about 0.2, and the best of each kind was
   selected among 8–1212 variants on the same primes, so the small wins are within the selection effect. Several
   kinds are clearly worse: LPS, and the integer lifts at Δ = 8 and 10 (by 0.5–0.9).
2. Arithmetic structure costs: LPS is about 0.8 worse than one random draw at q ≤ 113, and the gap grows like
   (1/3) log_p n (Theorem 3.2; card c14 measured slope 0.41 for LPS and −0.04 for random draws).
3. The records do not transport: the set that is a record at its own q (excess about 2.0) is an ordinary set at every
   other q (card c5). A record is a property of the pair (q, S), not of a formula.
4. Larger symmetry (k = 5, 6) is worse than k = 3 at the same Δ, for formulas and for random draws (card c15).
5. The records are about 1 below a single draw. In the model of [H] §3.5 a single random S misses about
   μ = N e^{−W/N} elements and is valid with probability about e^{−μ}; a search over T independent sets can afford
   μ* ≈ ln T, which lowers the needed W/N by about ln μ*, roughly one unit of log_{Δ−1} at the sizes of the records.
   A formula gives one set per q, so it cannot have this advantage unless it is better than random for structural
   reasons, as the Singer sets are at D = 3. We found no such structure at D ≥ 7.

---

## 6. Why no record-quality uniform family is in sight

**6.1 Fixed Δ, D → ∞.** By Proposition 1.1 a family here has q → ∞. A uniform family of record quality would have
diam ≤ log_{Δ−1} n + O(log log n) along an explicit sequence of groups. No explicit family of bounded-degree graphs with
diam ≤ (1 + ε) log_{Δ−1} n is known [secondary]; random Δ-regular graphs have diameter (1 + o(1)) log_{Δ−1} n
(B. Bollobás, W. Fernandez de la Vega, Combinatorica 2 (1982) 125–134 [secondary]), and so, conjecturally, do random
Haar graphs of SL(2, q) (research/theory/THRESHOLD.md, Conjecture 6, on master). The best explicit candidates, the
Ramanujan graphs, have almost all distances (1 + o(1)) log_{Δ−1} n (Sardari [abstract]; E. Lubetzky, Y. Peres, *Cutoff
on all Ramanujan graphs*, GAFA 26 (2016) [secondary]), but for the LPS graphs a few vertices are at distance
(4/3) log_p n (Theorem 3.2). That is the precise way in which the most natural uniform family of the records' shape
fails, and Corollary 3.4 turns it into a loss of a factor p^{D/4−1} against the Moore bound.

**6.2 Fixed D, Δ → ∞.** The LPS family with q ≈ p^{D/4} has degree p + 1 and order about p^{3D/4} at diameter ≈ D
(Corollary 3.4 is an upper bound; the lower side is Theorem 2.7, order p^{(D−O(1))/2}). Delorme's polygon constructions
reach a fixed fraction of p^{D−1} (§3). We know of no Haar-graph family of the records' groups that reaches
lim inf n·Δ^{1−D} > 0 at D = 8, 9 or 10; the random-S theorem of research/theory/THRESHOLD.md reaches
n ≥ Δ^{D−1}/((D − 1)!·(1 + η)·ln n) for every finite group, which loses a logarithm.

**6.3 What would change this.** A formula that beats one random draw by about 1 in excess, uniformly in q; or a
proof that some explicit cover (for example LPS × Z_m with labels given by a rule) has diameter
log_p n + O(log log n). Neither is in sight. The squads' round 2 looked for label rules for LPS × Z_m
(Appendix A).

---

## 7. Prior art

- **LPS graphs.** A. Lubotzky, R. Phillips, P. Sarnak, *Ramanujan graphs*, Combinatorica 8 (1988) 261–277; G. A.
  Margulis, Problems Inform. Transmission 24 (1988) 39–46 [secondary]; the book of Davidoff–Sarnak–Valette (2003)
  [secondary]. Definitions 2.1–2.2, Lemma 2.3, Theorem 2.7 and the factorization used in Theorem 3.2(b) are theirs.
- **The 4/3 lower bound.** Sardari (2019) [abstract], Remark 3.7.
- **Typical distances in Ramanujan graphs.** Lubetzky–Peres (2016) [secondary]; Sardari (2019) [abstract].
- **Haar graphs of SL(2, q) and PSL(2, q) in extremal problems.** [H] §6.1: Exoo–Jajcay (girth, a Haar graph of
  SL(2, 83)); Bray–Parker–Rowley (the group PSL(2, q) × Z_3); the LPS graphs themselves are Haar graphs of PSL(2, q) in
  the bipartite case (Lemma 2.5(d)). In the bipartite degree–diameter table at D = 8–10 (Miller–Širáň, DS14v2, 2013,
  as reproduced by the Combinatorics Wiki) we found no LPS graph; the novelty check `research/lit/novelty-2026-10-25.md`
  (branch `claude/novelty-literature-check-4i5frp`, claim 5) found no Haar graphs of SL(2, q) or PSL(2, q) there.
- **Asymptotic lower bounds for N^b(Δ, D).** Delorme (1985) [abstract via the novelty check]; random bipartite graphs
  (V. Klee, D. Larman, E. M. Wright, *The diameter of almost all bipartite graphs*, Studia Sci. Math. Hungar. 15 (1980)
  39–43 [secondary]); research/theory/THRESHOLD.md for random Haar graphs.
- **Orbit-closed connection sets.** [H] §6.1 (an old device; Singer sets and their multipliers).

What this note adds: Theorem 2.6 (the LPS sets have the records' orbit shape, with the cycle type computed), the
elementary proof and the exact value in Theorem 3.2, Corollary 3.4 in the form of a fraction of the Moore bound, the
covers of §4 and the measurements of §5. We claim no novelty for Lemmas 2.3–2.5 or for Theorem 2.7.

---

## 8. How to re-check

```bash
cd research/theorems/haar_families
cc -O3 -o lps_haar lps_haar.c -lm      # LPS graph: generators (-v), eccentricities, d(I, psi(i)) etc.
cc -O3 -o haar_ecc haar_ecc.c          # any Haar graph of SL/PSL/PGL(2,q) x Z_m from generator lines "a b c d z"
./lps_haar 5 13 -v                     # Example 2.8: 2184 vertices, diameter 7, d(I, psi(i)) = 6 = L0
python3 check_thmB.py 3,5,7,11,13,17,19,29 160 > recheck_thmB.log     # Computer-checked 3.5
python3 check_thmB_construction.py                                    # the beta of Theorem 3.2(b), q < 1000
./lps_haar 5 13 -v | grep '^gen' | sed 's/.*mat(//; s/) z=/ /; s/,/ /g' > g.txt
python3 component_edges.py pgl 13 1 e.txt < g.txt                    # independent edge list of the component
cc -O2 -o apsp ../../lifts/coordinator_check/apsp.c && ./apsp e.txt 6 40   # all-pairs BFS: diameter 7
python3 appendix_b.py                  # Appendix B from scan/lps_p*.txt (./scan_lps.sh p qmax rebuilds a scan)
python3 family_score.py --gen "./gen_lps.sh 5 {q}" --group pgl --qrange 23 113   # §5, LPS row
python3 ../../squads/thmfam-r1/c6/gen_c6.py 23 37 19 0 | ./haar_ecc pgl 23 37  # §4.2, (6,10)
python3 ../../squads/thmfam-r1/c6/gen_c6.py 23 37 19 0 | python3 verify_cover.py 23 37
python3 gen_lps_cover.py 7 11 151 cyc 1 57 | ./haar_ecc pgl 11 151           # §4.2, (8,8): diameter 8
python3 ../../squads/thmfam-r1/c7/c7lib.py 13 29 379 1 202 352 308 | ./haar_ecc pgl 29 379   # §4.2, (14,8)
```

---

## Appendix A. The squad rounds

Two rounds of Claude Haiku cards (the lab's `haiku-squad` skill; model haiku, effort high), directed by this session.
The cards, the shared rules and every card's code and notes are in `research/squads/thmfam-r1/` and
`research/squads/thmfam-r2/`, one line per card in `scoreboard.jsonl`; the rounds are logged in
`research/squads/LOG.md`. The squads searched constructions and tested the theorems on small q; the proofs are the
director's. Every number quoted in the note from a card was re-run by the director with the commands of §8, except
where it says "card" only (the mean excesses of §5, which are averages over many runs and are reproducible from the
cards' folders).

**Round 1 (18 cards): uniform families.** c1–c4 integer lifts (Δ = 6, 7, 8, 10, and with Z_m); c5 the records' sets at
other q; c6–c7 LPS × Z_m with searched labels; c8 verification of Theorems 2.6 and 3.2 (found a bug in the first
`lps_haar.c`); c9 the far vertices of LPS graphs (the guess "all far vertices come from pure quaternions" failed);
c10–c11 q-dependent formulas; c12 torus orbits with Δ ~ q; c13–c14 random baselines and the trend in q; c15 symmetries
of order 5 and 6; c16 the conic model; c17 cyclic factors with m ~ q; c18 repairs of LPS. Outcome: every formula family
is at the level of one random draw (§5); LPS × Z_m covers were the only direction that came close to the table (§4).

**Round 2 (11 cards): LPS × Z_m covers.** c1–c3 label rules (a formula in m) for p = 5, 7 and 11, 13; c4–c5 pushes of
p = 5 and p = 7 covers past the table with labels searched per (q, m); c6 Δ = 4 covers at (4,8), (4,9); c7 Δ = 12, 14
covers; c8 a numerical audit of §§1.2, 2, 3 and 4.1 of this note with its own code (one discrepancy, a miscount in the
first draft of Appendix B, now corrected; everything else passed, including the neighbourhood formulas of Example 2.8
against the edges, Lemma 2.5(c), Proposition 4.1 in covers and Corollary 3.4 on all 214 scan lines); c9 a second
quaternion algebra (Proposition 3.6); c10 random and exhaustive label baselines; c11 nonlinear arithmetic labels.
Outcome: the rules of c2 give the two members above the table in §4.3; nothing else beat the table. Searching
labels per (q, m) by hill climbing (c4, c5) did not beat the table either (one claimed (8,8) graph of c5 was not
connected within distance 8 and has diameter 9; the director's re-check caught it, and the card withdrew it). Fixed
rules recover part of the gain of a per-cell search at p = 5 and tie with random labels at p = 7, 11 (c1, c3, c10).

## Appendix B. The LPS family cell by cell

**Computer-checked** (`haar_families/appendix_b.py` from the scan logs `haar_families/scan/lps_p*.txt`, which list
the order and the diameter of Γ_{p,q} for every prime p < q up to the scan limit, computed by `lps_haar`). For each cell
the largest LPS graph of diameter ≤ D; A star (*) means the largest scanned q still had diameter ≤ D, so larger
LPS graphs may exist there. "Thm 3.2: q ≤" is the largest prime q with q² < 2p^{⌊D/2⌋}, the limit of Corollary 3.4.

| Δ (p) | D | q | vertices | % Moore | Thm 3.2: q ≤ | table | table / LPS | lab record |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| 4 (3) | 7 | 7 | 336 | 15.37 | 7 | 840 | 2.5 | 864 |
| 4 (3) | 8 | 7 | 336 | 5.12 | 11 | 2,184 | 6.5 | – |
| 4 (3) | 9 | 11 | 1,320 | 6.71 | 11 | 4,970 | 3.8 | – |
| 4 (3) | 10 | 13 | 2,184 | 3.70 | 19 | 11,748 | 5.4 | 12,416 |
| 4 (3) | 11 | 19 | 6,840 | 3.86 | 19 | – | – | – |
| 4 (3) | 12 | 19 | 6,840 | 1.29 | 37 | – | – | – |
| 6 (5) | 7 | 13 | 2,184 | 5.59 | 13 | 8,310 | 3.8 | 8,880 |
| 6 (5) | 8 | 23 | 12,144 | 6.22 | 31 | 29,790 | 2.5 | 31,680 |
| 6 (5) | 9 | 29 | 24,360 | 2.49 | 31 | 117,360 | 4.8 | 127,296 |
| 6 (5) | 10 | 53 | 148,824 | 3.05 | 79 | 452,032 | 3.0 | 524,160 |
| 6 (5) | 11 | 67 | 300,696 | 1.23 | 79 | – | – | – |
| 6 (5) | 12 | 107 | 1,224,936 | 1.00 | 173 | – | – | – |
| 8 (7) | 7 | 23 | 12,144 | 4.42 | 23 | 40,586 | 3.3 | 43,344 |
| 8 (7) | 8 | 31 | 29,760 | 1.55 | 67 | 201,480 | 6.8 | 239,904 |
| 8 (7) | 9 | 67 | 300,696 | 2.24 | 67 | 1,091,232 | 3.6 | 1,341,600 |
| 8 (7) | 10 | 107 | 1,224,936 | 1.30 | 181 | 6,927,210 | 5.7 | 7,818,096 |
| 8 (7) | 11 | 173 | 5,177,544 | 0.79 | 181 | – | – | – |
| 8 (7) | 12 | 229* | 12,008,760 | 0.26 | 479 | – | – | – |
| 12 (11) | 7 | 47 | 103,776 | 2.66 | 47 | 664,300 | 6.4 | 693,500 |
| 12 (11) | 8 | 71 | 357,840 | 0.83 | 167 | 4,650,100 | 13.0 | – |
| 12 (11) | 9 | 167 | 4,657,296 | 0.99 | 167 | 30,001,152 | 6.4 | 34,026,720 |
| 12 (11) | 10 | 251 | 15,813,000 | 0.30 | 563 | 300,383,050 | 19.0 | 325,832,976 |
| 12 (11) | 11 | 257* | 16,974,336 | 0.03 | 563 | – | – | – |
| 12 (11) | 12 | 257* | 16,974,336 | 0.00 | 1879 | – | – | – |
| 14 (13) | 7 | 59 | 205,320 | 1.96 | 61 | 1,771,560 | 8.6 | 1,789,588 |
| 14 (13) | 8 | 109 | 1,294,920 | 0.95 | 239 | 14,172,480 | 10.9 | – |
| 14 (13) | 9 | 233 | 12,649,104 | 0.72 | 239 | 95,087,738 | 7.5 | 116,068,656 |
| 14 (13) | 10 | 257* | 16,974,336 | 0.07 | 859 | 1,213,477,190 | 71.5 | 1,326,627,120 |
| 14 (13) | 11 | 257* | 16,974,336 | 0.01 | 859 | – | – | – |
| 14 (13) | 12 | 257* | 16,974,336 | 0.00 | 3089 | – | – | – |

Scan limits: p = 3: q ≤ 157, p = 5: q ≤ 157, p = 7: q ≤ 229, p = 11: q ≤ 257, p = 13: q ≤ 257.

At odd D, in the 13 cells not cut by the scan limit, the largest q reached equals the limit of Theorem 3.2 in 8 cells
((4,7), (4,9), (4,11), (6,7), (8,7), (8,9), (12,7), (12,9)), is the next prime below it in 3 ((6,9): 29 against 31;
(14,7): 59 against 61; (14,9): 233 against 239), and is farther below in 2 ((6,11): 67 against 79; (8,11): 173
against 181). So at odd D the vertex ψ(i) is usually what stops the family, as far as the scan goes. At even D = 2κ
the limit is the same as at D = 2κ + 1, and the generic vertices, at distance about log_p n, stop the family first.
