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
`claude/thm-haar-d8-10-sf7f0a`, cited below as [H]) are Haar graphs of SL(2, q) × $Z_{m}$ or PSL(2, q) × $Z_{m}$ whose
connection set S is closed under an automorphism of order 3, each found by computer search for one group. Can they be
turned into infinite families, with S given by one formula in q (and m) and a proved diameter?

**The answer, stated plainly.**

1. *There is an explicit infinite family of exactly this shape*, with m = 1: the connection sets of Lubotzky, Phillips
   and Sarnak (LPS). For every odd prime p and every prime q > p, the p + 1 LPS matrices in PGL(2, q) are permuted by
   conjugation with an element of order 3 of PSL(2, q), with cycle type 1+1+3+⋯+3 or 3+⋯+3: the cycle types that the
   orbit search used at Δ = 6, 8, 12, 14 (Theorem 2.6). Their diameter is at most 2 log_p n + O(1) (*cited*, LPS).
2. *This family provably cannot reach the records.* The vertex ψ(i) is at distance exactly the least even L with
   2p$^{L/2}$ > q² (Theorem 3.2: lower bound for every odd p, equality for p ≡ 1 mod 4), so the diameter is at least
   (4/3) log_p n − 2 log_p 2 (Corollary 3.3, the bound of N. T. Sardari, here with a two-paragraph proof), and a member
   of diameter ≤ D has at most √2·p$^{1−D/4}$ of the bipartite Moore bound (Corollary 3.4). Computed: the LPS graphs are
   2.4 to 15 times below the 2013 table at D = 8–10 (Appendix B).
3. *A cyclic factor removes this obstruction in practice, but not as a formula.* The obstruction survives every cover
   (Proposition 4.1), but it bounds q, not m. LPS × $Z_{m}$ with labels chosen for each (q, m) by a squad reaches 99.4 % of
   the table at (6,10) and 98.9 % at (8,8) (Computer-checked 4.2), still below the lab's records.
4. *Other uniform formulas behave like one random draw.* Integer lifts, primitive-root and Dickson formulas, the conic
   model and torus orbits (18 squad cards, §5) give an excess diam − $log_{Δ−1}$|G| of about 3.0–3.4 at Δ = 6–8, the same
   as a single random orbit-closed S, against about 2.0–2.3 for the records. Heuristically the records' advantage is
   selection among millions of sets, which no single formula provides (§5–6).
5. *What would be needed is open.* A uniform family of record quality at fixed Δ would be an explicit family of
   bounded-degree graphs with diameter (1 + o(1)) $log_{Δ−1}$ n. None is known; for the LPS graphs Sardari proved that it
   fails (§6).

No infinite family above the table is proved in this note.

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
| Prop. 1.1 | at fixed (Δ, D) only finitely many groups; for Q × $Z_{m}$ with Q perfect, m ≤ A(Δ, D) | Proposition (from [H]) |
| Lemma 2.3 | ψ: H(Z) → $M_{2}$($F_{q}$) is a ring homomorphism with kernel qH(Z); det ψ(α) = N(α); ψ(ᾱ) = adj ψ(α) | Lemma |
| Lemma 2.4 | for q > p the p + 1 matrices ψ(α), α ∈ $S_{p}$, are distinct in PGL(2, q), and ψ($S_{p}$) is closed under inversion | Lemma |
| Lemma 2.5 | structure of the component $Γ_{p,q}$; diam $Γ_{p,q}$ = ecc(I, A) | Lemma |
| Thm. 2.6 | conjugation by h = ψ(1+i+j+k), of order 3 in PSL(2, q), permutes ψ($S_{p}$) with cycle type 1+1+3$^{(p−1)/3}$ (p ≡ 1 mod 3), 3$^{(p+1)/3}$ (p ≡ 2 mod 3), 1+3 (p = 3) | Theorem |
| Thm. 2.7 | $Γ_{p,q}$ is connected and Ramanujan; diam ≤ 2 log_p n + O(1) | *cited* (LPS) |
| Lemma 3.1 | an even walk from (I, A) ends at ψ(β) with N(β) = p$^{L}$ and β ≡ 1 mod 2H(Z) | Lemma |
| Thm. 3.2 | d((I,A), (ψ(i),A)) ≥ L₀ := min{L even : 2p$^{L/2}$ > q²}, with equality if p ≡ 1 mod 4 | Theorem (equality uses a cited factorization) |
| Cor. 3.3 | diam $Γ_{p,q}$ > (4/3) log_p n − 2 log_p 2 | Corollary |
| Cor. 3.4 | if diam $Γ_{p,q}$ ≤ D then n < 2$^{3/2}$ p$^{3D/4}$ and n < √2·p$^{1−D/4}$·M$^{b}$(p+1, D) | Corollary |
| 3.5 | equality in Thm. 3.2 for all 8 primes p ≤ 29 tested (including p ≡ 3 mod 4) and all primes p < q ≤ 160; ecc − L₀ ∈ {0, 1, 2} | Computer-checked |
| Prop. 4.1 | the bound of Thm. 3.2 holds in every cover H(PGL(2,q) × K, S̃) of the LPS graph | Proposition |
| 4.2 | LPS × $Z_{m}$ with searched labels: 99.4 % of the table at (6,10), 98.9 % at (8,8) | Computer-checked |
| §5 | uniform formulas of six kinds: excess about that of one random draw | Computer-checked (scores), Heuristic (reading) |

---

## 1. Setting, notation and projective coordinates

### 1.1 Haar graphs

We use the conventions of [H] §1–2. For a finite group G and S ⊆ G with |S| = Δ, the Haar graph H(G, S) has vertex set
G × {A, B}, and (g, A) is adjacent to (sg, B) for every s ∈ S. It is bipartite and Δ-regular, the right translations
$ρ_{h}$(g, X) = (gh, X) are automorphisms acting regularly on each side ([H] Lemma 1.2), and its diameter is
max(ecc(e, A), ecc(e, B)) ([H] Cor. 2.3). A walk of length L from (e, A) uses letters $t_{1}$, …, $t_{L}$ ∈ S and ends at
(w, A) or (w, B) with

$$w = \cdots t_4^{-1}\, t_3\, t_2^{-1}\, t_1 \qquad (\text{an } A\text{-word}),$$

and the walk backtracks exactly when two consecutive letters are equal ([H] Prop. 2.2). Lemma 3.1 of [H]: H(G, S) is
isomorphic to H(G, aψ(S)$^{±1}$b) for a, b ∈ G and ψ ∈ Aut(G); the map (g, A) ↦ (g, B), (h, B) ↦ (h, A) is an
isomorphism H(G, S) → H(G, S⁻¹).

Throughout, M$^{b}$(Δ, D) = 2 $Σ_{j=0}$$^{D−1}$ (Δ − 1)$^{j}$ is the bipartite Moore bound, and n denotes the number of vertices of
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
3-cycles; for G = Q × $Z_{m}$ the automorphism is α(x, z) = (gxg⁻¹, rz) with g of order 3 modulo the centre of Q and r of
multiplicative order 3 mod m. The cycle types of the records are in [H] §5.1: 3+3 at (6,9), (6,10); 1+3+3 at Δ = 7;
1+1+3+3 at (8,8), (8,9), (8,10); 3+3+3 at (9,8), (9,9), (9,10); 3+3+3+3 at (12,9), (12,10); 1+1+3+3+3+3 at (14,9),
(14,10); and so on. Since |S| = f + 3c, f ≡ Δ (mod 3); every record with k = 3 uses the least such f ∈ {0, 1, 2}.

By a **uniform family** we mean, informally, one rule that produces S from q (and m) without a search for each q: a
formula, as for the Singer difference sets at D = 3. All the families below are uniform in this sense, except where a
search over labels is stated.

### 1.4 Where a uniform family can live

**Proposition 1.1.** (a) For fixed Δ ≥ 2 and D, only finitely many groups G admit S with |S| = Δ and
diam H(G, S) ≤ D. (b) If G = Q × $Z_{m}$ with Q perfect (for example Q = SL(2, q) or PSL(2, q), q ≥ 4) and diam H(G, S) ≤ D,
then m ≤ A(Δ, D) = Θ(D$^{Δ−1}$) for fixed Δ.

*Proof.* (a) |G| ≤ M$^{b}$(Δ, D)/2 ([H] Thm. 4.1). (b) [H] Cor. 4.4(ii). ∎

So an infinite uniform family of the records' shape has Δ fixed and D → ∞ (and then q → ∞, since m grows at most
polynomially in D while |G| must grow exponentially), or D fixed and Δ → ∞. The LPS family below can be read in both
regimes (Corollary 3.4).

---

## 2. The LPS family has the records' shape

### 2.1 Definitions

Let H(Z) = {a₀ + a₁i + a₂j + a₃k : $a_{t}$ ∈ Z} be the Lipschitz quaternions (i² = j² = k² = ijk = −1), with conjugate
ᾱ = a₀ − a₁i − a₂j − a₃k and norm N(α) = αᾱ = a₀² + a₁² + a₂² + a₃². N is multiplicative.

**Definition 2.1 (the LPS set).** For an odd prime p let $S_{p}$ be the set of α ∈ H(Z) with N(α) = p and

- if p ≡ 1 (mod 4): a₀ > 0 odd, and a₁, a₂, a₃ even;
- if p ≡ 3 (mod 4): a₀ even, a₁, a₂, a₃ odd, and either a₀ > 0, or a₀ = 0 and a₁ > 0.

By Jacobi's four-square theorem |$S_{p}$| = p + 1 (*cited*: LPS, Combinatorica 8 (1988), §2, and G. Davidoff, P. Sarnak,
A. Valette, *Elementary Number Theory, Group Theory and Ramanujan Graphs*, LMS Student Texts 55 (2003), Ch. 2
[secondary]). If α ∈ $S_{p}$ then ᾱ or −ᾱ is in $S_{p}$.

**Definition 2.2 (the splitting).** Let q be an odd prime, q ≠ p. Choose x, y ∈ $F_{q}$ with x² + y² + 1 = 0 (they exist:
the sets {x²} and {−1 − y²} both have (q + 1)/2 elements, so they meet). Put

$$\psi(a_0 + a_1 i + a_2 j + a_3 k) = \begin{pmatrix} a_0 + a_1 x + a_3 y & -a_1 y + a_2 + a_3 x \\ -a_1 y - a_2 + a_3 x & a_0 - a_1 x - a_3 y\end{pmatrix} \bmod q .$$

**Lemma 2.3.** ψ: H(Z) → $M_{2}$($F_{q}$) is a ring homomorphism with kernel qH(Z), and it is onto. det ψ(α) ≡ N(α), and
ψ(ᾱ) = adj ψ(α), so ψ(α)ψ(ᾱ) = N(α)·I.

*Proof.* ψ is additive and ψ(1) = I. Put $M_{i}$ = ψ(i) = [[x, −y], [−y, −x]], $M_{j}$ = ψ(j) = [[0, 1], [−1, 0]],
$M_{k}$ = ψ(k) = [[y, x], [x, −y]]. Direct multiplication gives $M_{i}$² = (x² + y²)·I = −I, $M_{j}$² = −I, $M_{i}$·$M_{j}$ = $M_{k}$ and
$M_{j}$·$M_{i}$ = [[−y, −x], [−x, y]] = −$M_{k}$. Since H(Z) is the ring generated over Z by i, j subject to i² = j² = −1 and
ji = −ij (with k = ij), the assignment i ↦ $M_{i}$, j ↦ $M_{j}$ extends to a ring homomorphism, and it sends k to
$M_{i}$·$M_{j}$ = $M_{k}$; this is the displayed formula. Its kernel contains qH(Z). If ψ(α) = 0, the diagonal gives a₀ + a₁x + a₃y = a₀ − a₁x − a₃y = 0, so a₀ = 0 and a₁x + a₃y = 0; the
off-diagonal gives a₂ = 0 and a₃x − a₁y = 0. Then a₁(x² + y²) = x(a₁x + a₃y) − y(a₃x − a₁y) = 0, so a₁ = 0 (x² + y² = −1),
and then a₃x = a₃y = 0 with (x, y) ≠ (0, 0), so a₃ = 0, all mod q. So the kernel is qH(Z), and the induced map
H(Z)/qH(Z) → $M_{2}$($F_{q}$) is injective between sets of size q⁴, hence onto. The determinant of the displayed matrix is
(a₀ + a₁x + a₃y)(a₀ − a₁x − a₃y) − (a₂ + a₃x − a₁y)(−a₂ + a₃x − a₁y) = a₀² − (a₁x + a₃y)² + a₂² − (a₃x − a₁y)²
= a₀² + a₂² − (a₁² + a₃²)(x² + y²) = N(α). Finally adj ψ(α) has diagonal (a₀ − a₁x − a₃y, a₀ + a₁x + a₃y) and
off-diagonal entries −(−a₁y + a₂ + a₃x), −(−a₁y − a₂ + a₃x), which is ψ(a₀ − a₁i − a₂j − a₃k). ∎

**Lemma 2.4.** Let q > p. (a) If α, β ∈ H(Z) have N(α) = N(β) = p and ψ(α) = cψ(β) for some c ∈ $F_{q}$^×, then α = ±β.
(b) The p + 1 points [ψ(α)], α ∈ $S_{p}$, of PGL(2, q) are distinct, and the set they form is closed under inversion.

*Proof.* (a) γ = αβ̄ has N(γ) = p², and ψ(γ) = ψ(α)ψ(β̄) = cψ(β)ψ(β̄) = cp·I. By Lemma 2.3, γ − c̃p ∈ qH(Z) for an
integer c̃ ≡ c, so the coordinates γ₁, γ₂, γ₃ are divisible by q. They are at most √N(γ) = p < q in absolute value, so
they vanish: γ is an integer with γ² = p², γ = ±p. Then α = γβ̄⁻¹ = ±pβ/N(β) = ±β. (b) Distinct elements of $S_{p}$ are
not negatives of each other (the sign conditions of Definition 2.1 fix the sign), so (a) gives distinctness. By
Lemma 2.3, [ψ(α)]⁻¹ = [adj ψ(α)] = [ψ(ᾱ)] = [ψ(±ᾱ)], and ±ᾱ ∈ $S_{p}$. ∎

**Definition 2.5'.** $Γ_{p,q}$ is the connected component of (I, A) in H(PGL(2, q), ψ($S_{p}$)).

**Lemma 2.5 (structure of $Γ_{p,q}$).** Let q > p and let c ∈ ψ($S_{p}$).

(a) All of ψ($S_{p}$) lies in one coset of PSL(2, q): in PSL(2, q) if p is a square mod q, in the other coset if not.
(b) The A-vertices of $Γ_{p,q}$ form H₀ × {A} for a subgroup H₀ ≤ PSL(2, q), and its B-vertices cH₀ × {B}. The right
translations $ρ_{h}$, h ∈ H₀, map $Γ_{p,q}$ to itself and act regularly on each side. When H₀ = PSL(2, q), $Γ_{p,q}$ has
n = q(q² − 1) vertices.
(c) diam $Γ_{p,q}$ = ecc(I, A) (computed in $Γ_{p,q}$).
(d) $Γ_{p,q}$ ≅ H(PSL(2, q), c⁻¹ψ($S_{p}$)) when it has q(q² − 1) vertices.

*Proof.* (a) det ψ(α) = p for all α (Lemma 2.3), and PSL(2, q) is the kernel of the homomorphism
PGL(2, q) → $F_{q}$^×/($F_{q}$^×)² induced by the determinant. (b) A letter and its inverse both have determinant class [p],
so an A-word of length L has class [p]$^{L}$: it lies in PSL(2, q) for L even and in cPSL(2, q) for L odd. The set H₀ of
the values of even A-words (the A-side of $Γ_{p,q}$) is closed under products and contains I, so it is a subgroup of the
finite group PSL(2, q). Right translation $ρ_{h}$ by h ∈ H₀ is an automorphism ([H] Lemma 1.2) mapping (I, A) to
(h, A) ∈ $Γ_{p,q}$, so it maps $Γ_{p,q}$ to itself; {$ρ_{h}$ : h ∈ H₀} acts regularly on the A-side H₀ × {A} and on the
B-side cH₀ × {B}. If $Γ_{p,q}$ is connected in the sense of Theorem 2.7, H₀ = PSL(2, q). (c) By (b) and [H] Lemma 2.1 (with the group {$ρ_{h}$ : h ∈ H₀}), diam $Γ_{p,q}$ = max(ecc(I, A), ecc(c, B)). Since ψ($S_{p}$) is closed under
inversion (Lemma 2.4), the side swap σ(g, A) = (g, B), σ(g, B) = (g, A) is an automorphism of H(PGL(2, q), ψ($S_{p}$))
([H] Lemma 3.1(iv)); and $ρ_{c}$ is one too. $ρ_{c}$∘σ maps (I, A) to (c, B) and maps $Γ_{p,q}$ onto the component of (c, B),
which is $Γ_{p,q}$ since (c, B) ~ (I, A). Hence ecc(c, B) = ecc(I, A). (d) The map (g, A) ↦ (g, A), (h, B) ↦ (c⁻¹h, B)
is the isomorphism H(G, S) → H(G, c⁻¹S) of [H] Lemma 3.1(i); restricted to $Γ_{p,q}$ it lands in
PSL(2, q) × {A, B}, and both graphs are Δ-regular with q(q² − 1) vertices. ∎

### 2.2 The order-3 symmetry

**Theorem 2.6.** Let p, q be odd primes, q > p, let ζ = 1 + i + j + k and h = ψ(ζ).

(a) h ∈ GL(2, q) has determinant 4, so [h] ∈ PSL(2, q), and [h] has order 3 in PGL(2, q).
(b) For every α ∈ H(Z), hψ(α)h⁻¹ = ψ(σ(α)), where σ(a₀ + a₁i + a₂j + a₃k) = a₀ + a₃i + a₁j + a₂k.
(c) Conjugation by h permutes the p + 1 points of ψ($S_{p}$). Its fixed points are the [ψ(α)] with a₁ = a₂ = a₃, and its
cycle type is

| p | cycle type on ψ($S_{p}$) | Δ = p + 1 | records with this cycle type ([H] §5.1) |
|---|---|---|---|
| p = 3 | 1 + 3 | 4 | none (Δ = 4 records are metacyclic) |
| p ≡ 1 (mod 3) | 1 + 1 + 3$^{(p−1)/3}$ | 8 (p = 7), 14 (p = 13), 20, 32, 38, … | (8,8), (8,9), (8,10); (14,9), (14,10) |
| p ≡ 2 (mod 3) | 3$^{(p+1)/3}$ | 6 (p = 5), 12 (p = 11), 18, 24, 30, … | (6,9), (6,10); (12,9), (12,10) |

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

(c) σ preserves the norm, the coordinate a₀ and the parity pattern of (a₁, a₂, a₃). If p ≡ 1 (mod 4), σ($S_{p}$) = $S_{p}$. If
p ≡ 3 (mod 4), σ(α) satisfies Definition 2.1 except possibly the sign rule when a₀ = 0, so σ(α) or −σ(α) lies in $S_{p}$,
and ψ(−β) = −ψ(β) is the same point of PGL(2, q). So conjugation by h permutes ψ($S_{p}$). By Lemma 2.4(a), [ψ(σα)] = [ψ(α)]
iff σ(α) = ±α. The case σ(α) = −α forces a₀ = 0 and (a₃, a₁, a₂) = (−a₁, −a₂, −a₃), so a₁ = −a₃ = a₂ = −a₁, so α = 0,
impossible. So the fixed points are the α ∈ $S_{p}$ with a₁ = a₂ = a₃ =: a, i.e. with a₀² + 3a² = p.

- If p ≡ 2 (mod 3), a₀² + 3a² ≡ a₀² ∈ {0, 1} (mod 3), so there is no fixed point.
- If p ≡ 1 (mod 3), the equation a₀² + 3a² = p has exactly four integer solutions (±a₀, ±a), with a₀, a ≠ 0 (Fermat;
  for a prime p ≡ 1 mod 3 the representation p = x² + 3y² with x, y > 0 is unique; *cited*: D. A. Cox, *Primes of the
  form x² + ny²*, Wiley 1989, §1 [secondary]). If p ≡ 1 (mod 4) then a₀ is odd and a even (odd + odd ≡ 0 and
  even + 3·odd ≡ 3 mod 4), so exactly the two solutions with a₀ > 0, namely a₀ + a(i + j + k) with a = ±|a|, are in
  $S_{p}$. If p ≡ 3 (mod 4) then a₀ is even and a odd, a₀ ≠ 0 (p ≠ 3a²), and again exactly the two with a₀ > 0 are in $S_{p}$.
  So there are two fixed points.
- If p = 3: a₀ = 0, a = ±1, and of ±(i + j + k) only i + j + k is in $S_{3}$. One fixed point.

Since [h] has order 3, every other point lies in a 3-cycle, which gives the cycle types. ∎

**Theorem 2.7 (*cited*: Lubotzky–Phillips–Sarnak, Combinatorica 8 (1988) 261–277 [secondary for the constants];
Davidoff–Sarnak–Valette (2003), Ch. 4 [secondary]).** Let p ≡ 1 (mod 4) and let q > p be an odd prime. Then
$Γ_{p,q}$ has q(q² − 1) vertices (that is, the LPS Cayley graph X$^{p,q}$ is connected), every eigenvalue of its adjacency
matrix other than ±(p + 1) has absolute value at most 2√p (Ramanujan), and diam $Γ_{p,q}$ ≤ 2 log_p n + O(1), with an
explicit constant given by LPS.

*Remark.* $Γ_{p,q}$ is X$^{p,q}$ itself when p is not a square mod q (X$^{p,q}$ is then a bipartite Cayley graph of
PGL(2, q), and a bipartite Cayley graph whose connection set lies in the non-trivial coset of an index-2 subgroup is a
Haar graph of that subgroup, Lemma 2.5(d)); it is the bipartite double cover of X$^{p,q}$ when p is a square mod q.
*Computer-checked*: $Γ_{p,q}$ has q(q² − 1) vertices for p ∈ {3, 5, 7, 11, 13} and every prime p < q ≤ 160 (logs
`haar_families/scan/lps_p*.txt`, column "vertices"), including p ≡ 3 (mod 4), which Theorem 2.7 as cited does not cover.

### 2.3 The family written out at Δ = 6

**Example 2.8 (p = 5).** $S_{5}$ = {1 ± 2i, 1 ± 2j, 1 ± 2k}. With x² + y² = −1 in $F_{q}$, the six matrices are

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
points of the first copy (by Lemma 2.3, adj ψ(α) = ψ(ᾱ), and S̄_5 = $S_{5}$, so the six adjugates are the same six
matrices up to scalars). For q = 13, with (x, y) = (0, 5) (the first solution of x² + y² + 1 ≡ 0 found by the
programs), the component of the first copy's identity is a 6-regular bipartite graph on 2184 vertices of diameter 7 (computer-checked by `lps_haar`, `haar_ecc` and the all-pairs BFS
`apsp.c`, §8).

---

## 3. The 4/3 obstruction

**Lemma 3.1 (walk values).** Let p, q be odd primes, q > p. A walk of even length L in H(PGL(2, q), ψ($S_{p}$)) from (I, A)
ends at a vertex ([ψ(β)], A) with β ∈ H(Z), N(β) = p$^{L}$ and β ≡ 1 (mod 2H(Z)); in particular the real coordinate b₀ of
β is odd.

*Proof.* The walk with letters ψ($α_{1}$), …, ψ($α_{L}$) ends at $s_{L}$⁻¹s_{L−1}⋯$s_{2}$⁻¹s_1 with $s_{t}$ = ψ($α_{t}$), and
[ψ(α)⁻¹] = [ψ(ᾱ)] (Lemma 2.3). So it ends at [ψ(β)] with β = ᾱ_L $α_{L−1}$ ⋯ ᾱ_2 $α_{1}$, and N(β) = p$^{L}$. Reduce mod 2: in
H(Z)/2H(Z) we have −1 = 1, so i, j, k commute there. If p ≡ 1 (mod 4), every $α_{t}$ and ᾱ_t is ≡ 1 (mod 2H(Z)), so β ≡ 1.
If p ≡ 3 (mod 4), every $α_{t}$ and ᾱ_t is ≡ v := i + j + k, and v² = i² + j² + k² + 2(ij + jk + ki) ≡ 1, so β ≡ v$^{L}$ = 1
since L is even. ∎

**Theorem 3.2 (distance to ψ(i)).** Let p, q be odd primes with q > p, and let L₀ be the least even integer L ≥ 0 with
2p$^{L/2}$ > q². In $Γ_{p,q}$:

(a) d((I, A), ([ψ(i)], A)) ≥ L₀, and the same holds for ψ(j) and ψ(k);
(b) if p ≡ 1 (mod 4), equality holds.

Note that det ψ(i) = N(i) = 1, so [ψ(i)] ∈ PSL(2, q) for every q.

*Proof.* (a) A path from (I, A) to ([ψ(i)], A) has even length L (the graph is bipartite). By Lemma 3.1 there is β with
N(β) = p$^{L}$, b₀ odd and [ψ(β)] = [ψ(i)], i.e. ψ(β) = cψ(i) with c ∈ $F_{q}$^×. By Lemma 2.3, β − c̃i ∈ qH(Z), so
q | b₀, b₂, b₃. Put P = p$^{L/2}$, an integer. Since b₀ is odd, b₀ ≠ 0, so b₀² ≥ q², and then
b₁² = P² − b₀² − b₂² − b₃² ≤ P² − q², so |b₁| < P. Also q² divides b₀² + b₂² + b₃² = P² − b₁² = (P − b₁)(P + b₁). The
prime q does not divide P (q ≠ p), so q cannot divide both factors (it would divide their sum 2P). Hence q² divides
P − εb₁ for some ε ∈ {1, −1}. Since |b₁| < P, 0 < P − εb₁ < 2P, so q² ≤ P − εb₁ < 2P. That is 2p$^{L/2}$ > q², and
L ≥ L₀. For ψ(j) and ψ(k): conjugation by h fixes (I, A), is an automorphism of H(PGL(2, q), ψ($S_{p}$)) (Theorem 2.6 and
[H] Prop. 3.3(a)), and maps [ψ(i)] to [ψ(j)] to [ψ(k)] (Theorem 2.6(b)), so the three distances are equal.

(b) Let L = L₀, P = p$^{L/2}$, and put n₁ = 2P − q² > 0. Here P ≡ 1 (mod 4) (p ≡ 1 mod 4), so 2P ≡ 2 (mod 8), and
q² ≡ 1 (mod 8), so n₁ ≡ 1 (mod 8). By the Gauss–Legendre three-square theorem (*cited*; n is a sum of three squares
unless n = 4$^{a}$(8b + 7)), n₁ = u² + v² + w² with integers u, v, w; since n₁ ≡ 1 (mod 4), exactly one of them is odd, and
we name it u. Put

$$\beta = qu + (P - q^2)\,i + qv\,j + qw\,k .$$

Then N(β) = q²(u² + v² + w²) + (P − q²)² = q²(2P − q²) + P² − 2Pq² + q⁴ = P² = p$^{L}$; b₀ = qu is odd, b₁ = P − q² is even,
and b₂ = qv, b₃ = qw are even; so β ≡ 1 (mod 2H(Z)). And β ≡ P·i (mod qH(Z)), so [ψ(β)] = [Pψ(i)] = [ψ(i)]. By the
LPS factorization theorem (*cited*: LPS 1988 §3; Davidoff–Sarnak–Valette (2003), Ch. 2, the unique factorization of
quaternions β ≡ 1 mod 2 of norm p$^{L}$ [secondary]), β = ±p$^{r}$ $α_{1}$α_2⋯$α_{L−2r}$ with $α_{t}$ ∈ $S_{p}$ and r ≥ 0. Since
[ψ(±p$^{r}$ γ)] = [ψ(γ)], we get [ψ(i)] = [ψ($α_{1}$⋯$α_{L'}$)] with L' = L − 2r even. Choose the letters
$s_{1}$ = ψ($α_{L'}$), $s_{2}$ = ψ(ᾱ_{L'−1}) (so [$s_{2}$⁻¹] = [ψ($α_{L'−1}$)]), $s_{3}$ = ψ($α_{L'−2}$), $s_{4}$ = ψ(ᾱ_{L'−3}), …; they lie in
ψ($S_{p}$) up to sign (Lemma 2.4(b)), and the A-word $s_{L'}$⁻¹ ⋯ $s_{2}$⁻¹s_1 has value [ψ($α_{1}$⋯$α_{L'}$)]. So there is a walk of
length L' ≤ L₀ from (I, A) to ([ψ(i)], A). With (a), the distance is L₀. ∎

**Corollary 3.3.** For odd primes q > p, with n = q(q² − 1) ≥ |V($Γ_{p,q}$)|:

$$\operatorname{diam}\Gamma_{p,q} \;\ge\; L_0 \;\ge\; 4\log_p q - 2\log_p 2 \;>\; \tfrac43 \log_p n - 2\log_p 2 .$$

*Proof.* 2p$^{L₀/2}$ > q² gives L₀ > 2 log_p(q²/2) = 4 log_p q − 2 log_p 2, and n < q³. ∎

**Corollary 3.4 (a vanishing fraction of the Moore bound).** Let p be an odd prime, D ≥ 2, and q > p a prime with
diam $Γ_{p,q}$ ≤ D. Then q² < 2p$^{⌊D/2⌋}$, the number of vertices satisfies

$$n \le q(q^2-1) < 2^{3/2}\, p^{\frac32\lfloor D/2\rfloor} \le 2^{3/2} p^{3D/4},$$

and n < √2·p$^{1−D/4}$·M$^{b}$(p + 1, D). In particular, along the LPS family the fraction of the Moore bound tends to 0
both for fixed p and D → ∞ and for fixed D ≥ 5 and p → ∞.

*Proof.* L₀ ≤ diam ≤ D and L₀ is even, so L₀ ≤ 2⌊D/2⌋ and 2p$^{⌊D/2⌋}$ ≥ 2p$^{L₀/2}$ > q². Then n < q³ < (2p$^{⌊D/2⌋}$)$^{3/2}$.
Finally M$^{b}$(p + 1, D) = $2Σ_{j<D}$ p$^{j}$ > 2p$^{D−1}$, so n/M$^{b}$ < 2$^{3/2}$p$^{3D/4}$/(2p$^{D−1}$) = √2·p$^{1−D/4}$. ∎

For comparison: at D = 8 the bound is √2/p (28 % for p = 5), and the LPS graphs actually reach 1–6 % (Appendix B);
the lab's records at D = 8 are at 8–22 %, and the D = 8 table values with Δ ≥ 10 (Gómez's compounds of generalized
hexagons) at about 10 % ([H] §5, §6). In the regime D fixed, Δ → ∞, Delorme's constructions from generalized polygons
have lim inf n·Δ$^{1−D}$ > 0 for every D (C. Delorme, J. Graph Theory 9 (1985) 325–334 [abstract]), so arithmetic Haar
families lose to them by a factor p$^{D/4−1}$.

**Computer-checked 3.5.** For p ∈ {3, 5, 7, 11, 13, 17, 19, 29} and every prime q with p < q ≤ 160, the distance from
(I, A) to ([ψ(i)], A), ([ψ(j)], A) and ([ψ(k)], A), computed by breadth-first search (`lps_haar.c`), equals L₀: no
exception in [[$N_{THMB}$]] cases (log `haar_families/recheck_thmB.log`). This includes p ≡ 3 (mod 4), where equality is
not proved here. The eccentricity of (I, A) exceeds L₀ by 0, 1 or 2 ([[ECC_DIST]]). So in this range the special vertex
ψ(i) alone accounts for the diameter up to at most 2. An independent re-implementation by squad card c8 (its own
quaternion arithmetic and BFS; `research/squads/thmfam-r1/c8/`) confirmed Theorem 2.6(c) for all 137 pairs with
7 ≤ q ≤ 61 and Theorem 3.2 in 41 cases with q ≡ 1 (mod 4), and its all-pairs BFS (`apsp.c`) agreed with `haar_ecc` on six
LPS graphs. (The squad card also found a bug in the first version of `lps_haar.c`, which mixed the distances of the
two sides; the logs above are from the corrected version.)

**Remark 3.6 (prior art).** The lower bound (4/3) log_p n + O(1) for the diameter of the bipartite LPS graphs is due to
N. T. Sardari, *Diameter of Ramanujan graphs and random Cayley graphs*, Combinatorica 39 (2019) 427–446,
arXiv:1511.09340 [abstract]; his abstract also states that almost all pairs of vertices of a Ramanujan graph are at
distance at most (1 + ε) $log_{p}$ n, and reports numerics in which LPS diameters grow like (4/3) log and those of random
Cayley graphs like log. We did not read his proof; the argument above is short and may be his. The exact value in
Theorem 3.2(b) follows from the same arithmetic and the LPS factorization; we did not check whether it is stated
there. That the LPS sets are permuted by the Hurwitz unit (1 + i + j + k)/2 is classical; we found no source that
compares their cycle types with orbit-searched connection sets, and claim nothing more than the observation.

---

## 4. Cyclic factors

**Proposition 4.1.** Let K be a finite group, κ: $S_{p}$ → K any map, and S̃ = {(ψ(α), κ(α)) : α ∈ $S_{p}$} ⊆ PGL(2, q) × K.
Then for every k ∈ K, the distance in H(PGL(2, q) × K, S̃) from (I, $e_{K}$, A) to ([ψ(i)], k, A) is at least L₀. Hence if
the component of (I, $e_{K}$, A) has diameter ≤ D and contains ([ψ(i)], k, A) for some k, then q² < 2p$^{⌊D/2⌋}$.

*Proof.* The projection (g, k, X) ↦ (g, X) maps every edge {(g, k, A), (ψ(α)g, κ(α)k, B)} to the edge
{(g, A), (ψ(α)g, B)}, so it maps walks to walks of the same length and does not decrease distances. Apply
Theorem 3.2(a). ∎

So a cyclic factor cannot help at the vertex ψ(i) with a fixed q; what it changes is that m is free. The order is
q(q² − 1)·m, the obstruction bounds only q, and the counting bound ([H] Thm. 4.1) allows m up to about
p$^{D−1}$/q³. Whether the cyclic part can be filled efficiently is a computational question:

**Computer-checked 4.2 (squad cards c6, c7).** Let r have order 3 mod m. Labels α ↦ z(α) ∈ $Z_{m}$ that are equivariant for
the order-3 symmetry (z(σα) = r·z(α); fixed letters get 0; one 3-cycle gets (1, r, r²) without loss of generality, the
others (t, rt, r²t)) make H(PGL(2, q) × $Z_{m}$, S̃) orbit-closed with α(x, z) = (hxh⁻¹, rz), exactly the records' shape.
Searching t for each (q, m), the squads found:

| cell | best LPS × $Z_{m}$ (q, m) | vertices | of table | lab record | LPS alone (Appendix B) |
|---|---|---:|---:|---:|---:|
| (6,8) | (13, 13) | 28,392 | 95.3 % | 31,680 | 12,144 |
| (6,9) | (13, 43) | 93,912 | 80.0 % | 127,296 | 24,360 |
| (6,10) | (23, 37) | 449,328 | 99.4 % | 524,160 | 148,824 |
| (8,8) | (11, 151) | 199,320 | 98.9 % | 239,904 | 29,760 |
| (8,9) | [[$C7_{89}$]] | | | 1,341,600 | 300,696 |

Every entry was re-checked with `haar_ecc` (two-source BFS on the component) and, for (6,10), with
`verify_cover.py` (independent Python arithmetic; eccentricities 10 and 10). These graphs are below the lab's records
and below the table, and their labels were searched for each (q, m): they are not a uniform family. They show that the
cyclic factor removes most of the 4/3 loss in practice: at (6,10) the cover is 3.0 times the LPS graph alone.

---

## 5. Other uniform families (squad round 1)

**Score.** For a family S(q) and the primes 23 ≤ q ≤ 113, the *excess* is diam − $log_{Δ−1}$|G| with |G| = one side of
the graph, averaged over q (`haar_families/family_score.py`, which runs `haar_ecc`). Lower is better. A uniform family
gets one S per q, so it should be compared with *one* random orbit-closed draw per q, not with the records, which are
the best of millions of evaluations for one (q, m).

**Computer-checked 5.1 (mean excess, 22 primes 23 ≤ q ≤ 113, group PSL(2, q) unless stated; from
`research/squads/thmfam-r1/scoreboard.jsonl`).**

| family | Δ | mean excess | random orbit-closed draw, same Δ | card |
|---|---|---:|---:|---|
| LPS, p = 5 (component of PGL(2, q)) | 6 | 4.00 | 3.18–3.50 (3 seeds) | director |
| integer lifts, O(X) ∪ O(Y), X, Y ∈ SL(2, Z), entries ≤ 3 (best of 206) | 6 | 3.36 | 3.18–3.50 | c1 |
| integer lifts, {I} ∪ O(X) ∪ O(Y) (best of 1212; mean of top 10: 3.35) | 7 | 3.10 | 2.96–3.24 (5 seeds, mean 3.07) | c2 |
| primitive-root formulas, e.g. X = [[g, 1], [0, g⁻¹]], Y = [[1/2, g], [g, 2(1 + g²)]] (best of 16) | 7 | 2.96 | 2.96–3.24 | c10 |
| Dickson / trace / power formulas (best of 15) | 6 | 3.13 | 3.18–3.50 | c11 |
| conic model, Cayley transforms of integer matrices (best of 8) | 8 | 3.34 | 3.25–3.30 | c16 |
| order-5 or order-6 symmetry, single orbits (k = 6, best) | 12 | 2.73 | k = 3: 2.55–2.64; k = 6: 2.91–3.09 | c15 |
| LPS + one extra α-orbit (repair) | 9 | 3.24 (7 primes) | 2.72–2.86 | c18 |
| [[MORE_ROWS]] | | | | |
| the lab's records (one (q, m) each, annealed) | 6–16 | about 2.0–2.3 | | [H] |

Torus-orbit families with Δ growing like q (card c12: S = {I} ∪ T-conjugates of x for a torus T of PSL(2, q)) have
diameter 5 to 7 for 31 ≤ q ≤ 61 and reach at most 1.8 % of the Moore bound at their diameter; no family of diameter
≤ 4 appeared. The excess of LPS grows with log_5|G| with slope 0.41 (card c14, 38 primes 23 ≤ q ≤ 199; Corollary 3.3
predicts 1/3), that of random orbit-closed draws with slope −0.04.

**Heuristic 5.2 (reading of 5.1).**

1. The best uniform formula of each kind ties a single random draw; it does not beat it by more than the spread of
   random seeds (about 0.1–0.2), and the "best" was selected among 8–1212 variants on the same primes.
2. Arithmetic structure costs: LPS is about 0.6–0.8 worse than one random draw at q ≤ 113, and the gap grows like
   (1/3) log_p n (Theorem 3.2, card c14).
3. Larger symmetry (k = 5, 6) is worse than k = 3 at the same Δ, for formulas and for random draws (card c15), in line
   with [H] §3.5: orbit closure helps the search, not the quality of a single set.
4. The records are about 1 below a single draw. In the model of [H] §3.5 a single random S misses about
   μ = N e$^{−W/N}$ elements and is valid with probability about e$^{−μ}$; the search raises the usable μ to μ* with
   e$^{μ*}$ ≈ the number of independent tries, which shrinks the needed W/N by ln μ*, about one unit of
   $log_{Δ−1}$. A formula gives one try per q.

---

## 6. Why no record-quality uniform family is in sight

**6.1 Fixed Δ, D → ∞.** By Proposition 1.1 a family here has q → ∞. A uniform family of record quality would have
diam ≤ $log_{Δ−1}$ n + O(log log n) along an explicit sequence of groups. No explicit family of bounded-degree graphs with
diam ≤ (1 + ε) $log_{Δ−1}$ n is known [secondary]; random Δ-regular graphs have diameter (1 + o(1)) $log_{Δ−1}$ n
(B. Bollobás, W. Fernandez de la Vega, Combinatorica 2 (1982) 125–134 [secondary]), and so, conjecturally, do random
Haar graphs of SL(2, q) (research/theory/THRESHOLD.md, Conjecture 6, on master). The best explicit candidates, the
Ramanujan graphs, have almost all distances (1 + o(1)) $log_{Δ−1}$ n (Sardari [abstract]; E. Lubetzky, Y. Peres, *Cutoff
on all Ramanujan graphs*, GAFA 26 (2016) [secondary]), but for the LPS graphs a few vertices are at distance
(4/3) log_p n (Theorem 3.2). That is the precise way in which the most natural uniform family of the records' shape
fails, and Corollary 3.4 turns it into a loss of a factor p$^{D/4−1}$ against the Moore bound.

**6.2 Fixed D, Δ → ∞.** The LPS family with q ≈ p$^{D/4}$ has degree p + 1 and order about p$^{3D/4}$ at diameter ≈ D
(Corollary 3.4 is an upper bound; the lower side is Theorem 2.7, order p$^{(D−O(1))/2}$). Delorme's polygon constructions
reach a fixed fraction of p$^{D−1}$ (§3). We know of no Haar-graph family of the records' groups that reaches
lim inf n·Δ$^{1−D}$ > 0 at D = 8, 9 or 10; the random-S theorem of research/theory/THRESHOLD.md reaches
n ≥ Δ$^{D−1}$/((D − 1)!·(1 + η)·ln n) for every finite group, which loses a logarithm.

**6.3 What would change this.** A formula that beats one random draw by about 1 in excess, uniformly in q; or a
proof that some explicit cover (for example LPS × $Z_{m}$ with labels given by a rule) has diameter
log_p n + O(log log n). Neither is in sight. The squads' round 2 looked for label rules for LPS × $Z_{m}$
(Appendix A).

---

## 7. Prior art

- **LPS graphs.** A. Lubotzky, R. Phillips, P. Sarnak, *Ramanujan graphs*, Combinatorica 8 (1988) 261–277; G. A.
  Margulis, Problems Inform. Transmission 24 (1988) 39–46 [secondary]; the book of Davidoff–Sarnak–Valette (2003)
  [secondary]. Definitions 2.1–2.2, Lemma 2.3, Theorem 2.7 and the factorization used in Theorem 3.2(b) are theirs.
- **The 4/3 lower bound.** Sardari (2019) [abstract], Remark 3.6.
- **Typical distances in Ramanujan graphs.** Lubetzky–Peres (2016) [secondary]; Sardari (2019) [abstract].
- **Haar graphs of SL(2, q) and PSL(2, q) in extremal problems.** [H] §6.1: Exoo–Jajcay (girth, a Haar graph of
  SL(2, 83)); Bray–Parker–Rowley (the group PSL(2, q) × $Z_{3}$); the LPS graphs themselves are Haar graphs of PSL(2, q) in
  the bipartite case (Lemma 2.5(d)). In the bipartite degree–diameter table at D = 8–10 (Miller–Širáň, DS14v2, 2013,
  as reproduced by the Combinatorics Wiki) we found no LPS graph; the novelty check `research/lit/novelty-2026-10-25.md`
  (branch `claude/novelty-literature-check-4i5frp`, claim 5) found no Haar graphs of SL(2, q) or PSL(2, q) there.
- **Asymptotic lower bounds for N$^{b}$(Δ, D).** Delorme (1985) [abstract via the novelty check]; random bipartite graphs
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
./lps_haar 5 13 -v | grep '^gen' | sed 's/.*mat(//; s/) z=/ /; s/,/ /g' > g.txt
python3 component_edges.py pgl 13 1 e.txt < g.txt                    # independent edge list of the component
cc -O2 -o apsp ../../lifts/coordinator_check/apsp.c && ./apsp e.txt 6 40   # all-pairs BFS: diameter 7
python3 table_lps.py                   # Appendix B from scan/lps_p*.txt
python3 family_score.py --gen "./gen_lps.sh 5 {q}" --group pgl --qrange 23 113   # §5, LPS row
python3 ../../squads/thmfam-r1/c6/gen_c6.py 23 37 19 0 | ./haar_ecc pgl 23 37  # §4.2, (6,10)
python3 ../../squads/thmfam-r1/c6/gen_c6.py 23 37 19 0 | python3 verify_cover.py 23 37
```

---

## Appendix A. The squad rounds

[[SQUADS]]

## Appendix B. The LPS family cell by cell

[[APPB]]
