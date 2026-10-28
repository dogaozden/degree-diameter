# Gómez's compound graphs ΩH_q and the diameter-8 entries of the bipartite table

Degree–diameter lab (Claude Code sessions coordinated by Doğa Özden), github.com/dogaozden/degree-diameter.
Draft, 28 October 2026, for Gabriela Araujo-Pardo and Ignacio López. Job paper-omega, branch
`claude/omega-d8-note-xrbqux`. Typeset version: `research/theorems/omega_note/OMEGA_NOTE.pdf` (source `OMEGA_NOTE.tex`
in the same folder, built with tectonic). This note replaces the one-page note of 26 October
(`papers/Ozden_OmegaH_D8_note.pdf`) and adds the full proofs and the results on relabelled copies.

**Labels.** Every claim carries one of these labels.

- **Theorem**: proved by hand in this note; the proof is complete. *Theorem (computer-assisted)*: the proof is complete
  except for one named Computer-checked statement.
- **Computer-checked**: a statement about finite data, with the programs and logs that check it (§8). "Twice" means by
  two programs written separately, in different sessions, sharing no code.
- **Heuristic**: an argument with a named gap. It is not a proof.
- **Fact**: a standard result, quoted with a reference.

Theorem 1 is also formalised in Lean 4 (§3).

## 0. Summary

Six D = 8 entries of the bipartite degree–diameter table (Miller–Širáň 2013, Table 4, as reproduced on the
CombinatoricsWiki, credited to Delorme–Gómez–Quisquater) are the orders of Gómez's compound graphs ΩH_q [Gó86, §2.9.3,
values on p. 46]. Here H(q) is the split Cayley hexagon, its incidence graph has N₁ = 2N vertices with
N = (q⁶−1)/(q−1), and q + 3 = 2α + β with β ∈ {0, 1}:

| cell | table value | graph | q | α | copies of I(H(q)) | hubs | order 5(α+1)N₁ |
|---|---:|---|---:|---:|---:|---:|---:|
| (10,8) | 1,176,480 | ΩH₇ | 7 | 5 | 25 | 196,080 | 1,176,480 |
| (11,8) | 2,246,940 | ΩH₈ | 8 | 5 | 25 | 374,490 | 2,246,940 |
| (12,8) | 4,650,100 | ΩH₉ | 9 | 6 | 30 | 664,300 | 4,650,100 |
| (14,8) | 14,172,480 | ΩH₁₁ | 11 | 7 | 35 | 1,771,560 | 14,172,480 |
| (15,8) | 14,172,480 | ΩH₁₁ (value of (14,8) reused) | 11 | 7 | 35 | 1,771,560 | 14,172,480 |
| (16,8) | 36,201,060 | ΩH₁₃ | 13 | 8 | 40 | 4,022,340 | 36,201,060 |

The thesis states D ≤ D₁ + 2 = 8 and gives no proof. The paper the table cites (Delorme, Gómez, Quisquater, "On large
bipartite graphs") was never published, as far as we could find. The results:

1. **Theorem 1 (one label; also in Lean).** A projection argument: if a new vertex is joined only to copies of one
   vertex t of B₁ and misses a copy, it is at distance ≥ d_{B₁}(t, v) + 3 from the copy of v in the missed copy. In one
   reading of the figures (reading 2) this gives diam ΩH_q ≥ 9 for every q and every pairing of labels.
2. **Theorem 2 (two labels, q ≥ 7).** For the thesis's labelling (every copy carries the same labels) and every reading
   of the figures, every hub has at least q⁵ − 5q⁴ − 8q³ − 12q² − 16q − 10 vertices at distance ≥ 9 in every copy
   it misses. This covers the six table entries. By computer, ΩH₇ and ΩH₉ have diameter exactly 9 (C2).
3. **Theorems 3 and 4 (geometric relabellings, q ≥ 7).** Give every copy its own labelling, and call it geometric if
   every transfer map between two copies met by one hub class is induced by an automorphism of the incidence graph of
   H(q). For every q ≥ 7, every geometric labelling, every reading and every mix of block types, the diameter is still
   ≥ 9. For q ≥ 10 the proof is by hand; for q = 8, 9 it uses a computer count of route words (C4), and for q = 7 also
   Bonferroni inequalities and a character-sum bound (Theorem 4).
4. **Open (§6).** Arbitrary (non-geometric) relabellings, for every q ≥ 4: at q = 2 and q = 3 such relabellings do give
   diameter 8 (C7), and no argument excludes them at the table's q. Labellings chosen per hub class and copy. Other
   wirings. The geometric class at q ≤ 5 (computations only).
5. **What can be claimed (§7).** The six entries have no checkable graph of diameter 8. We do not claim that no
   (Δ, 8) graph of these orders exists.

## 1. The split Cayley hexagon

### 1.1 Coordinates

We use the model of our diameter-7 note [ÖD7, §1.1]; all of the lab's generators use it. Let q be a prime power,
F = F_q and V = F⁷ with coordinates (X₀, …, X₆). Put

  Q(X) = X₀X₄ + X₁X₅ + X₂X₆ − X₃²,  b(X, Y) = Q(X+Y) − Q(X) − Q(Y) = X₀Y₄ + X₄Y₀ + X₁Y₅ + X₅Y₁ + X₂Y₆ + X₆Y₂ − 2X₃Y₃.

The parabolic quadric Q(6, q) is the set of points ⟨x⟩ of PG(6, q) with Q(x) = 0. Two points ⟨x⟩, ⟨y⟩ of Q(6, q) are
*perpendicular*, x ⊥ y, if b(x, y) = 0; since Q(λx + μy) = λμ b(x, y), this means that the line xy lies on Q(6, q).
For a point x, x^⊥ is the hyperplane b(x, ·) = 0.

The split Cayley hexagon H = H(q) [Ti59; VM98, §2.4] has

- points: the set P of all N = (q⁶−1)/(q−1) points of Q(6, q);
- lines: the set L of the lines of Q(6, q) whose Grassmann coordinates p_ij = x_i y_j − x_j y_i (for two spanning
  points x, y) satisfy p₁₂ = p₃₄, p₅₄ = p₃₂, p₂₀ = p₃₅, p₆₅ = p₃₀, p₀₁ = p₃₆, p₄₆ = p₃₁;
- incidence: containment.

For example, the q + 1 lines through e₀ = (1, 0, …, 0) are ⟨e₀, λe₅ + μe₆⟩, (λ : μ) ∈ PG(1, q); they lie in the totally
singular plane ⟨e₀, e₅, e₆⟩. The incidence graph I = I(q) has vertex set P ∪ L, 2N vertices; d denotes its distance,
S_i(z) = {u : d(z, u) = i}, B(z, R) = {u : d(z, u) ≤ R}, and opp(z) = S₆(z) (the elements *opposite* z).

**Fact 1.1** [Ti59; VM98, §2.4]. H(q) is a generalized hexagon of order (q, q): I is connected, bipartite,
(q+1)-regular, of diameter 6 and girth 12. The lines of H(q) through a point x are the lines through x of a totally
singular plane π_x ⊂ x^⊥.

**Fact 1.2** [Ti59; VM98]. The automorphisms of I that fix P are the collineations of H(q). They form the group
G₂(q) ⋊ Aut(F_q) and are induced by semilinear maps of V preserving Q; for q prime every collineation is induced by a
linear map in G₂(q) ≤ SO(7, q) (an isometry of Q of determinant 1). For example, for A ∈ SL(3, q) the map
(v, a, w) ↦ (Av, a, A^{−T}w), where x = (v, a, w) with v = (x₀, x₁, x₂), a = x₃, w = (x₄, x₅, x₆), is in G₂(q). An
automorphism of I exchanging P and L (a *duality*) exists if and only if q is a power of 3.

**Fact 1.3** (eigenvalues in G₂). For h ∈ G₂(q) acting on V, the eigenvalues of h (in the algebraic closure, with
multiplicity) are 1, x₁^{±1}, x₂^{±1}, x₃^{±1} with x₁x₂x₃ = 1. (The semisimple part of h is conjugate over F̄_q into
the maximal torus diag(a, b, c, 1, a⁻¹, b⁻¹, c⁻¹), abc = 1, of the subgroup SL(3) above; the characteristic polynomial
of h is that of its semisimple part.)

### 1.2 Distances

**Lemma 1.4 (Theorem; distance profile).** Let t, u be vertices of I with d(t, u) = k.

(a) If 1 ≤ k ≤ 5, exactly one neighbour of u is at distance k − 1 from t and the other q are at distance k + 1. If
k = 6, all q + 1 neighbours of u are at distance 5 from t.

(b) A walk (u₀, u₁, …, u_i) with u_{j+1} ≠ u_{j−1} for all j ("non-backtracking") and i ≤ 6 has d(u₀, u_i) = i. For
i ≤ 5, each vertex of S_i(u₀) is the end of exactly one such walk. Hence |S_i(u)| = s_i := (q+1)q^{i−1} for 1 ≤ i ≤ 5,
|S₆(u)| = q⁵, s₀ := 1.

*Proof.* (a) I is bipartite, so the neighbours of u are at distance k ± 1, and at k − 1 only when k ≥ 1; since the
diameter is 6, they are all at distance 5 when k = 6. For 1 ≤ k ≤ 5 at least one neighbour is at distance k − 1 (the
previous vertex of a geodesic). If two were, there would be two distinct geodesics from t to u, and their union would
contain a cycle of length ≤ 2k ≤ 10 < 12. (b) By induction on j, using (a) with t := u₀: if (u₀, …, u_j) is a geodesic
and 1 ≤ j ≤ 5, then u_{j−1} is the unique neighbour of u_j at distance j − 1 from u₀, so u_{j+1} ≠ u_{j−1} is at
distance j + 1. For i ≤ 5 the geodesic from u₀ to a vertex of S_i(u₀) is unique by the same girth argument. The count
follows, and |S₆(u)| = 2N − 1 − Σ_{i=1}^{5} (q+1)q^{i−1} = q⁵. ∎

**Lemma 1.5 (Theorem; orthogonality) [VM98, §2.4].** For points x, y of H(q): d(x, y) ≤ 4 if and only if x ⊥ y. So
opp(x) ∩ P = P ∖ x^⊥.

*Proof.* If d(x, y) ≤ 4, there is a point z with x and y on lines of H through z (z = x if d(x, y) ≤ 2). These lines lie
in the totally singular plane π_z (Fact 1.1), so b(x, y) = 0. Conversely, x^⊥ ∩ Q(6, q) is a cone with vertex x over a
Q(4, q), so it has 1 + q(q³ + q² + q + 1) points, and by Lemma 1.4 there are 1 + s₂ + s₄ = 1 + q(q+1) + q³(q+1) points at
distance ≤ 4 from x. The two numbers are equal, so the inclusion is an equality. ∎

**Lemma 1.6 (Theorem; opposite elements in balls).** Let t, z be vertices of I of the same type, d = d(t, z). Then

  |B(z, 4) ∩ opp(t)| = 0 if z = t, and q⁴ if d ∈ {2, 4, 6};
  |B(z, 2) ∩ opp(t)| = 0 if d ∈ {0, 2}, and q² if d ∈ {4, 6}.

*Proof.* The vertices of B(z, 4) of the type of t are at even distance i ∈ {0, 2, 4} from z. By Lemma 1.4(b) the
vertices of S_i(z) correspond to the non-backtracking walks z = h₀, h₁, …, h_i, and we follow d(t, h_j) along the walk
with Lemma 1.4(a): from h_j at distance k ∈ [1, 5] from t, if h_{j−1} is the neighbour at distance k − 1 ("we came up")
all q choices of h_{j+1} go up to k + 1; if h_{j−1} is at distance k + 1 ("we came down"), one choice goes down to k − 1
and q − 1 go up; from distance 6 all choices go down to 5.

- d = 0: B(t, 4) misses opp(t).
- d = 2: from distance 2, four steps reach distance 6 only if every step goes up: q (first step, avoiding the one
  down-neighbour) times q³; so q⁴ vertices of S₄(z) are opposite t, and none of B(z, 2).
- d = 4: i = 2: both steps up, q · q = q². i = 4: if h₁ goes down (1 way, to distance 3), h₂ must go up (q − 1 ways; going
  down reaches distance 2) and then h₃, h₄ up (q² ways): (q−1)q². If h₁ goes up (q ways, distance 5), h₂ goes up to 6
  (q ways), h₃ goes down to 5 (q ways), and h₄ ≠ h₂ must go up: h₃ has one neighbour at distance 4 and h₂ is at
  distance 6, so q − 1 ways: q³(q−1). Total q² + (q−1)q² + (q−1)q³ = q⁴; and B(z, 2) gives q².
- d = 6: i = 0 gives 1. i = 2: h₁ at distance 5 (q + 1 ways), then h₂ ≠ z: one neighbour of h₁ is at distance 4 and z is
  at 6, so q − 1 ways to reach 6: (q+1)(q−1). i = 4: if h₂ is the neighbour of h₁ at distance 4, then h₃ ≠ h₁ goes up to 5
  in q − 1 ways (one goes down), and h₄ ≠ h₂ goes up to 6 in all q ways (h₂ is h₃'s only neighbour at distance 4):
  (q+1)(q−1)q. If h₂ is at distance 6 (q − 1 ways), h₃ is at 5 (q ways) and h₄ ≠ h₂ reaches 6 in q − 1 ways:
  (q+1)(q−1)q(q−1). Total for i = 4: (q+1)(q−1)q², and 1 + (q² − 1) + (q⁴ − q²) = q⁴; B(z, 2) gives 1 + q² − 1 = q². ∎

(The same counts for every radius ≤ 4 and both types follow from the intersection array
{q+1, q, q, q, q, q; 1, 1, 1, 1, 1, q+1} of I, which is distance-regular; the referee of the relabelling note computed
them that way, `logs/lemma31_drg.txt`.)

## 2. Gómez's construction

### 2.1 The text

J. Gómez Martí, *Diámetro y vulnerabilidad en redes de interconexión*, PhD thesis, ETSE Telecomunicación, Universitat
Politècnica de Catalunya, 1986 [Gó86]. We read the scan on F. Comellas's site (161 pages, 8,989,821 bytes; for thesis
pages 33 onwards, PDF page = thesis page + 6). The construction is §2.9.3, pp. 43–45, verbatim:

> p. 43: "2.9.3 En esta construcción, que da lugar a grafos bipartitos, también se toman, como en los Apartados 2.8.4 y
> 2.8.9, copias de K₁, (vértices aislados). Sin embargo la estructura de interconexión es algo distinta de las
> anteriores en el sentido de que el diámetro resultante no está acotado por D₀ + D₁ + 1 = D₁ + 1 sino por D₁ + 2."
>
> p. 44: "Tomemos primeramente 5 copias de un grafo bipartito B₁ con diámetro D₁ par y 10 conjuntos de N₁ vértices cada
> uno. Cada 10 vértices —uno de cada conjunto— se unen a las copias de B₁ según muestra la Figura 2.21.a, [figure] de
> manera que su grado queda igual a dos. Ahora incrementamos dicho grado hasta 4, uniendo estos vértices a 5 copias de
> B₁ según la Figura 2.21.b.
>
> El grafo bipartito así construido tiene N = 10·N₁/2 + 10N₁ = 15N₁ vértices, grado Δ = max{4, Δ₁+2} y diámetro
> D ≤ D₁ + 2. En general, si Δ₁ + 2 = 2α + β, α ≥ 2, β = 0, 1, se toman 5α copias de B₁ de manera, que, utilizando
> cualquiera de las dos estructuras anteriores el grado de los vértices correspondientes a las copias de K₁ se
> incrementa hasta 2α. Entonces se obtiene un grafo bipartito, que denotamos por ΩB₁, con parámetros
> N = 10·N₁/2 + 5αN₁ = 5(α+1)N₁, Δ = Δ₁ + 2 y D ≤ D₁ + 2."

In English: take 5 copies of a bipartite graph B₁ of even diameter D₁ and 10 sets of N₁ vertices each [the count
shows that N₁/2 is meant]; every 10 vertices, one from each set, are joined to the copies as in Fig. 2.21a, so that
their degree is 2; then raise the degree to 4 by joining them to 5 more copies as in Fig. 2.21b. In general, if
Δ₁ + 2 = 2α + β, take 5α copies, using either of the two structures, so that the copies of K₁ get degree 2α; the
result ΩB₁ has N = 5(α+1)N₁, Δ = Δ₁ + 2 and D ≤ D₁ + 2.

No proof is given. §2.8.2 (p. 30) says the proofs of this part are left out: "prescindiendo de las demostraciones que,
aunque son largas, no ofrecen ninguna dificultad pues se basan en las mismas ideas desarrolladas hasta ahora". The list
on p. 46 includes ΩH₅: N(8,8) ≥ 195 300; ΩH₇: N(10,8) ≥ 1 176 480; ΩH₈: N(11,8) ≥ 2 246 940; ΩH₉: N(12,8) ≥ 4 650 100;
ΩH₁₁: N(14,8) ≥ 14 172 480; ΩH₁₁d: N(15,8) ≥ 14 978 080; ΩH₁₃: N(16,8) ≥ 36 201 060. Here H_q is the incidence graph of
H(q): D₁ = 6, Δ₁ = q + 1, N₁ = 2N. ΩH₁₁d is not defined in §§2.7–2.9; the table's (15,8) value is |ΩH₁₁|.

### 2.2 Labels

§2.7.1 (p. 21): "Supongamos que los vértices del conjunto V_ij están rotulados con los elementos del conjunto Z/n_iZ."
Both colour classes of B₁ are labelled by Z/n₁Z, n₁ = N₁/2, and every adjacency rule of §§2.7–2.9 is written in these
labels, the same in every copy. §2.8.9 (p. 39), which §2.9.3 cites for its copies of K₁, defines them as
"(t, i), t ∈ {0, 1, …, n₁−1}, i ∈ {0, 1, …, 4}", and Fig. 2.18 (p. 41) joins vertex (t, 1, j, k, h) of copy (B₁, k, h)
to (t, i), as in "(t,1,0,0,0) ∼ (t,0)": **a copy of K₁ with label t is joined only to vertices labelled t**, in either
colour class. For B₁ = I(H(q)) we write the labelling as two bijections P₀: Z/NZ → P (the point labelled t) and
L₀: Z/NZ → L (the line labelled t). The thesis does not fix them; σ = L₀P₀⁻¹ (point t ↦ line t) is an arbitrary
bijection P → L.

### 2.3 The figures

Both figures put five copies of B₁ at the corners of a pentagon, inside a circle and a pentagram (Fig. 2.21a: copies
B₁⁰ … B₁⁴ clockwise from the top; Fig. 2.21b: B₁^0̄ … B₁^4̄). Each copy is drawn with a dashed line (its two colour
classes) and two dots: an *outer* dot on the circle and an *inner* dot at the corner of the pentagram. Every K₁-vertex
of the block is a dot on an arc or on a pentagram edge, joined to the two dots at its ends. In Fig. 2.21a the K₁-vertex
k lies on the pentagram edge between copies k − 1 and k + 1 and k̄ on the arc between copies k + 2 and k + 3; in
Fig. 2.21b, k lies on the arc between copies k + 3 and k + 4 and k̄ on the pentagram edge between copies k − 1 and
k + 1 (indices mod 5). So every copy vertex gets two new edges and every K₁-vertex two per block.

The figures do not say which colour class the inner dot is. In Figs. 2.3, 2.6 and 2.18 the class above the dashed line
is class j = 0, and in both Figs. 2.21 the outer dot of the top copy is above the dashed line. With class 0 = points this
gives **reading 1**: outer = points and inner = lines in every copy. **Reading 2** (used by the first computations):
unbarred K₁-vertices always on points and barred ones always on lines. Neither figure says which blocks are of
type (a) and which of type (b) ("utilizando cualquiera de las dos estructuras"), so we allow any pattern. Below we allow
the inner class to be chosen freely in every copy; this contains both readings and their duals.

### 2.4 Definition with exact neighbourhoods

**Definition 2.1 (ΩH_q).** Data: a prime power q, α = ⌊(q+3)/2⌋; a block pattern (τ₀, …, τ_{α−1}) ∈ {a, b}^α; an inner
class ι(c) ∈ {P, L} for every copy c; and a *labelling*, that is, bijections P_c: Z/NZ → P and L_c: Z/NZ → L for every
copy c.

- *Copies.* c = 5B + i with block B ∈ {0, …, α−1} and position i ∈ Z₅; 5α copies. Copy vertices (c, x), x ∈ P ∪ L, with
  (c, x) ∼ (c, y) when x and y are incident.
- *Hubs* (the copies of K₁). (t, k) and (t, k̄) for t ∈ Z/NZ (the *row*) and k ∈ Z₅; the hub *classes* are
  k = {(t, k)} (unbarred) and k̄ = {(t, k̄)} (barred).
- *Copies met by a class* (positions mod 5):
  C(k) = {5B + k − 1, 5B + k + 1 : τ_B = a} ∪ {5B + k + 3, 5B + k + 4 : τ_B = b},
  C(k̄) = {5B + k + 2, 5B + k + 3 : τ_B = a} ∪ {5B + k − 1, 5B + k + 1 : τ_B = b}.
- *Where a class sits.* In copy c of a block of type a, unbarred classes sit on the inner class ι(c) and barred classes on
  the outer class; in a block of type b, unbarred on the outer and barred on the inner class.
- *Hub edges.* (t, Y) ∼ (c, P_c(t)) if Y sits on points in c, and (t, Y) ∼ (c, L_c(t)) if Y sits on lines in c, for
  every c ∈ C(Y).

The **thesis labelling** is P_c = P₀, L_c = L₀ for all c. **Reading 1**: ι(c) = L for all c. **Reading 2**: ι(c) = P in
a-blocks and L in b-blocks (then unbarred hubs sit on points everywhere). The graph ΩH_q of the thesis is the thesis
labelling with any pattern and either reading.

*Exact neighbourhoods.* Write m_c(t) for the inner mark of row t in copy c (P_c(t) if ι(c) = P, L_c(t) if ι(c) = L) and
m̄_c(t) for the outer mark. Then, for c = 5B + i:

| vertex | neighbours |
|---|---|
| (c, x) | (c, y) for the q + 1 elements y incident with x; and two hubs: |
| — τ_B = a, x = m_c(t) | (t, i − 1), (t, i + 1) |
| — τ_B = a, x = m̄_c(t) | (t, (i+2)‾), (t, (i+3)‾) |
| — τ_B = b, x = m_c(t) | (t, (i−1)‾), (t, (i+1)‾) |
| — τ_B = b, x = m̄_c(t) | (t, i + 1), (t, i + 2) |
| (t, k) | (5B + k ∓ 1, m_{5B+k∓1}(t)) for τ_B = a; (5B + k + 3, m̄(t)), (5B + k + 4, m̄(t)) for τ_B = b |
| (t, k̄) | (5B + k + 2, m̄(t)), (5B + k + 3, m̄(t)) for τ_B = a; (5B + k ∓ 1, m(t)) for τ_B = b |

(in the hub rows the mark is taken in the copy named in the same pair).

**Lemma 2.2 (Theorem; parameters).** For every pattern, inner classes and labelling, ΩH_q is a simple bipartite graph
on 10(α+1)N = 5(α+1)N₁ vertices; copy vertices have degree q + 3 and hubs degree 2α, so Δ = q + 3 = Δ₁ + 2; it has
5αN(q+1) + 20αN edges. Every hub meets 2α of the 5α copies and misses 3α.

*Proof.* A copy at position i of an a-block is met by the unbarred classes i ± 1 and the barred classes i + 2, i + 3; of
a b-block, by the unbarred classes i + 1, i + 2 and the barred classes i ± 1. So each copy is met by exactly two classes
of each bar, the two of one bar sit on the same type, and each class has one hub per row. Every element x of a copy is
the mark of exactly one row of its type, so it gets exactly two hubs. A class meets two distinct copies in each block.
For the colouring, give unbarred hubs colour 0, in every copy the type on which the unbarred classes sit colour 1 and
the other type colour 0, and barred hubs colour 1: copy edges join a point and a line, so every edge has ends of two
colours. ∎

## 3. Theorem 1: one label (also in Lean)

**Theorem 1 (projection).** Let B be a graph and G a graph whose vertices are of two kinds: *copy vertices* v, each
with a copy index c(v) ∈ J and a label f(v) ∈ V(B), and *new vertices* x, each with a label f(x) ∈ V(B). Assume

- (h1) if u ∼ w are copy vertices, then c(u) = c(w) and f(u) ∼ f(w) in B;
- (h2) every neighbour w of a new vertex x is a copy vertex with f(w) = f(x);
- (h3) no two new vertices are adjacent.

If x is a new vertex with no neighbour in copy j, and v is a copy vertex with c(v) = j, then
d_G(x, v) ≥ d_B(f(x), f(v)) + 3.

*Proof.* Let (x = w₀, w₁, …, w_ℓ = v) be a walk. By (h2), w₁ is a copy vertex with f(w₁) = f(x). Let m be the number
of new vertices among w₁, …, w_{ℓ−1}. A new vertex w_i (0 < i < ℓ) has copy vertices w_{i−1}, w_{i+1} on both sides, with
f(w_{i−1}) = f(w_i) = f(w_{i+1}) by (h2); every other edge w_iw_{i+1} (i ≥ 1) joins two copy vertices and maps to an edge
of B by (h1). Deleting the m new vertices and one of the two equal labels around each, the labels of w₁, …, w_ℓ form a
walk in B from f(x) to f(v) of length ℓ − 1 − 2m. So ℓ ≥ d_B(f(x), f(v)) + 1 + 2m. If m = 0, then w₁, …, w_ℓ are copy
vertices joined by copy edges, so by (h1) c(w₁) = c(v) = j, and w₁ is a neighbour of x in copy j, a contradiction. So
m ≥ 1 and ℓ ≥ d_B(f(x), f(v)) + 3. ∎

**Lean.** `BipartiteDD.LeanMaxx.Projection.edist_ge` in `lean/BipartiteDD/LeanMaxx/Projection/Main.lean` (branch
`claude/leanmaxx-projection-r0kehl`, commit 50cc900; walk lemmas in `Walk.lean`). Copies are encoded by
`c : V → Option ι` (`none` = new vertex) and labels by `f : V → β`:

```lean
theorem edist_ge
    (h1 : ∀ u w i j, G.Adj u w → c u = some i → c w = some j → i = j ∧ B.Adj (f u) (f w))
    (h2 : ∀ x w, G.Adj x w → c x = none → c w ≠ none ∧ f w = f x)
    (h3 : ∀ x w, G.Adj x w → c x = none → c w = none → False)
    {x v : V} (hx : c x = none) {j : ι} (hmiss : ∀ w, G.Adj x w → c w ≠ some j)
    (hv : c v = some j) :
    (B.dist (f x) (f v) + 3 : ℕ∞) ≤ G.edist x v
```

with the corollary `ediam_ge` ((D₁ + 3 : ℕ∞) ≤ G.ediam when B.edist t s = D₁, f x = t, f v = s). `#print axioms` gives
only `propext`, `Classical.choice`, `Quot.sound`. An independent session rebuilt the module (Lean v4.34.1, Mathlib as
pinned), regenerated the axioms output byte for byte, grepped for `sorry`/`admit`/`native_decide`, and read the
statement against the card (`research/lean-maxx/VERIFY.md`, branch `claude/leanmaxx-verify-9ummw2`, commit 2ff0c8e).
The Lean statement is slightly more general than the one above (B need not be bipartite, copies need not be whole
copies; `B.dist` is 0 when f x and f v are not connected, which only weakens it). The check that ΩH_q satisfies h1–h3 is
Corollary 3.1 below; it is not part of the Lean files.

**Corollary 3.1 (Theorem).** Take the thesis labelling and inner classes for which every hub class sits on one type in
all copies it meets (reading 2; its dual; reading 1 when all blocks have one type). Then for every q, every pattern and
every pairing σ: every hub x and every copy j that x misses, the q⁵ vertices (j, y) with y opposite the mark of x are at
distance ≥ 9 from x. So diam ΩH_q ≥ 9. More generally, for any bipartite B₁ with a pair of vertices at distance D₁, ΩB₁
in reading 2 has diameter ≥ D₁ + 3.

*Proof.* Label copy vertices by f(c, y) = y and c(c, y) = c, and a hub by its mark (P₀(t) or L₀(t), the same in all
copies by assumption). Copy edges satisfy (h1), hub edges (h2) by Definition 2.1, and there are no hub–hub edges. Every
hub misses 3α ≥ 1 copies (Lemma 2.2). Every vertex of I has q⁵ opposite vertices (Lemma 1.4). Apply Theorem 1. For a
general B₁, in reading 2 the unbarred classes sit on all labels of class 0 and the barred classes on all labels of
class 1, so whichever class holds the pair, some hub carries one of its labels. ∎

**Computer-checked C1 (the hexagons).** The incidence graphs of H(q) used below were built and checked by all-pairs
BFS (no symmetry assumed): 2N vertices, bipartite, (q+1)-regular, diameter 6, girth 12 (sphere sizes s_i from every
vertex). Three times: `hexq6.c` (this model) with `apsp_mt` for q = 3, 4, 5, 7, 8, 9, 11, 13 (own-12-8); `hexgen.c`,
`hexgf.c` (split octonions) with `bitapsp.c` for q = 2, 3, 4, 5, 7, 8, 9, 11, 13 (referee omega-dq); `buildhex.py`
(split octonions) with `ghcheck.c` for q = 3, 7, 8, 9 (referee omega-repair). A (q+1)-regular bipartite graph on 2N
vertices with diameter 6 and girth 12 is the incidence graph of a generalized hexagon of order (q, q).

**Computer-checked C2 (the thesis graphs).**
(a) *Exact diameters* (both block types present): ΩH₃ and ΩH₅ (195,300 vertices, the thesis's (8,8) value): 9 by
all-pairs BFS, both readings, σ = identity and two random σ, patterns aba, aab, abab, aabb (twice: own-12-8,
`apsp_auto`; referee omega-dq, `bitapsp`). ΩH₇ (1,176,480): 9 in reading 2 (ababa) and in reading 1 (ababa, random σ),
by BFS from 117,648 sources, one in every orbit of the rotation and the block swaps, each automorphism checked edge by
edge (referee omega-dq). ΩH₉ (4,650,100): 9 in reading 2 (aaabbb; 18 orbits of a group generated by the rotation, block
swaps, a Singer cycle and a transvection of H(9), all checked on the 27,900,600 edges) and in reading 1 (Singer-
equivariant σ, 4,380 orbits) (own-12-8); again 9 in reading 2 and in reading 1 with a random σ from 398,580 orbit
representatives (referee omega-dq).
(b) *All six thesis values*: BFS from a hub gives eccentricity 9 for ΩH₅, ΩH₇, ΩH₈, ΩH₉, ΩH₁₁, ΩH₁₃ at the thesis
orders, both readings (twice: own-12-8 `omega_bfs`; referee omega-dq `omegaref`, and a third time by the table audit
for reading 1). In reading 2 the vertices at distance 9 from hub (t, k) are exactly the points opposite t in the 3α
copies it misses (3α·q⁵: 252,105 at q = 7, 491,520 at q = 8, 1,062,882 at q = 9, 3,382,071 at q = 11, 8,911,032 at
q = 13).
(c) *One block type*: diameter 10 (all pairs at q = 2, 3, 5; orbit BFS at q = 7, 9).
(d) Explicit pairs at distance 9 for every cell: `research/projects/table-audit/checks/witness_omega_thesis.txt`
(branch claude/table-audit-2-p7x6hn), `research/d12D8/omega/witness_pairs.txt` (own-12-8).

## 4. Theorem 2: two labels

In reading 1 with both block types, an unbarred hub (t, k) meets line L₀(t) in a-blocks and point P₀(t) in b-blocks,
so Theorem 1 does not apply. The following count covers every reading.

**Theorem 2.** Let q ≥ 7. Take ΩH_q with the thesis labelling, any block pattern and any inner classes (so both readings
and every pairing σ). Let x be a hub and j a copy that x misses. Then at least

  q⁵ − (A + B + 1) = q⁵ − 5q⁴ − 8q³ − 12q² − 16q − 10 > 0

vertices of copy j are at distance ≥ 9 from x, where

  A = Σ_{e₁+e₂ ∈ {0,2,4}} s_{e₁}s_{e₂} = 5q⁴ + 8q³ + 6q² + 4q + 2,  B = Σ_{e₁+e₂+e₃ ≤ 2} s_{e₁}s_{e₂}s_{e₃} = 6q² + 12q + 7

(sums over e_i ≥ 0, s_i as in Lemma 1.4). In particular diam ΩH_q ≥ 9.

| q | A | B | A + B + 1 | q⁵ | far vertices per missed copy (≥) |
|---:|---:|---:|---:|---:|---:|
| 7 | 15,073 | 385 | 15,459 | 16,807 | 1,348 |
| 8 | 24,994 | 487 | 25,482 | 32,768 | 7,286 |
| 9 | 39,161 | 601 | 39,763 | 59,049 | 19,286 |
| 11 | 84,625 | 865 | 85,491 | 161,051 | 75,560 |
| 13 | 161,449 | 1,177 | 162,627 | 371,293 | 208,666 |

*Proof.* Let τ be the involution of P ∪ L with τ(P₀(s)) = L₀(s) for every row s. Every hub (s, ·) is adjacent, in each
copy it meets, to P₀(s) or to L₀(s) (Definition 2.1 with the thesis labelling). Let x have row t, and let T ∈ {P, L} be
the type of the vertices of copy j that have the colour of x's neighbours (Lemma 2.2: in each copy, one type has that
colour). Let z = P₀(t) if T = P and z = L₀(t) if T = L. We show that at most A + B + 1 elements w ∈ opp(z) have
d(x, (j, w)) ≤ 8; since |opp(z)| = q⁵, the rest are at distance ≥ 9.

Fix w ∈ opp(z) of type T. G is bipartite and (j, w) has the colour of x's neighbours, so d(x, (j, w)) is odd; suppose it
is ≤ 7 and take a shortest path. It leaves x to a vertex (c₁, a₀) with a₀ ∈ {z, τ(z)}, then alternates walks inside
copies with passes copy → hub → copy. A pass through a hub of row s goes from (c, a) to (c′, a′) with
a, a′ ∈ {P₀(s), L₀(s)}, so a′ = a (a *stay*) or a′ = τ(a) (a *switch*). Since x misses j there is at least one pass. With
e copy edges and p ≥ 1 passes the length is 1 + e + 2p ≤ 7 and odd, so e is even, e ≤ 4 and p ≤ 3 − e/2. Let r ≤ p be
the number of switches. Merging the stays, the sequence of labels is a walk in I from a₀, of e edges in total, with τ
applied r times in between, ending at w. Every edge of I and every switch changes the type, and w has the type of z, so
r is even if a₀ = z and odd if a₀ = τ(z).

The set of ends of walks of length f from a vertex u is ⋃ S_g(u) over g ≤ f with g ≡ f (mod 2), of size at most the sum
of the s_g. So:

- a₀ = z, r = 0: w is the end of a walk of length e ≤ 4 from z, so d(z, w) ≤ 4 and w ∉ opp(z).
- a₀ = z, r = 2: p ≥ 2, so e ≤ 2; the label walk is z → (f₁ edges) → u₁, switch, → (f₂) → u₂, switch, → (f₃) → w,
  f₁ + f₂ + f₃ = e ≤ 2. At most B such w.
- a₀ = τ(z), r = 1: τ(z) → (f₁) → u₁, switch, → (f₂) → w with f₁ + f₂ = e ∈ {0, 2, 4}. At most A such w.
- a₀ = τ(z), r = 3: p = 3, e = 0, and w = τ⁴(z) = z ∉ opp(z). (We count it as 1 to match the earlier reports.)

So at most A + B + 1 elements of opp(z) are within distance 7 of x. The closed forms are direct expansions (for A:
s₀s₀ + 2s₀s₂ + s₁s₁ + 2s₀s₄ + 2s₁s₃ + s₂s₂). Finally, for q ≥ 7, q⁴(q − 5) ≥ 2q⁴ ≥ 14q³, so
q⁵ − 5q⁴ − 8q³ − 12q² − 16q − 10 ≥ 6q³ − 12q² − 16q − 10 ≥ 30q² − 16q − 10 > 0. ∎

*Remark.* The proof uses only: G bipartite; all copies carry the labels P₀, L₀; every hub of row s is adjacent, in each
copy it meets, only to P₀(s) or L₀(s); no hub–hub edges; x misses a copy. It does not use that x meets both types, so it
also covers the hubs to which Theorem 1 applies. (This corrects two points of the first write-up, as its referee asked:
"bipartite" belongs in the hypothesis, and the appeal to Theorem 1 for single-label hubs is not needed.) For q ≤ 6 the
count is not enough (A + B + 1 > q⁵); see C3.

**Corollary 4.1 (Theorem).** As defined in the thesis (every copy carries the same labels, a copy of K₁ with label t is
joined only to vertices labelled t), ΩH_q has diameter ≥ 9 for q = 7, 8, 9, 11, 13, under every reading of
Figs. 2.21a/b, every pattern of block types and every pairing of point labels with line labels. These are the six table
entries.

**Computer-checked C3 (q = 3, 5).** Where Theorem 2's count fails, all-pairs BFS gives diameter 9 for ΩH₃ and ΩH₅ in both
readings and with several σ (C2(a)). Under reading 1 (σ the identity or random), the largest number of opposite vertices of the right
type within distance 7 of a hub, in a copy it misses, was 7,562–8,039 at q = 7 (bound 15,459), 13,950 at q = 8 (25,482),
22,771–22,825 at q = 9 (39,763), 52,372 at q = 11 (85,491) and 104,225 at q = 13 (162,627) (referee omega-dq).

## 5. Relabelling the copies

Diameter ≥ 9 comes from the shared labels. A labelling that differs from copy to copy is not in the thesis (§§2.7–2.9
use one labelling for all copies), but it is the obvious repair, and at q = 2, 3 it works (C7). This section shows that
it cannot work at the table's q with labellings that respect the geometry.

### 5.1 The model

A labelling (P_c, L_c) as in Definition 2.1 gives each copy one point labelling and one line labelling, used by every
hub class of the corresponding type that meets the copy. For a hub class Y and copies c, d ∈ C(Y), the **transfer**
T_Y(c → d) maps the mark of row t in c to the mark of row t in d: it is P_d P_c⁻¹, L_d L_c⁻¹, L_d P_c⁻¹ or P_d L_c⁻¹,
depending on the types Y sits on in c and d.

**Definition 5.1.** A labelling is **geometric** if every transfer is the restriction (to P or to L) of an automorphism
of I, that is, of a collineation of H(q) or (when q is a power of 3) a duality.

(Labellings chosen per pair (class, copy), where the two classes of one bar meeting a copy may use different
bijections, are outside this model even when every transfer is a collineation; see §6.)

**Lemma 5.2 (Theorem; one automorphism per copy).** Relabelling every copy c of a graph ΩH_q by an automorphism g_c of I
(replacing every vertex (c, y) by (c, g_c(y))) gives an isomorphic graph. In particular, if P_c = g_c P₀ and L_c = g_c L₀
with collineations g_c (or dualities, with the inner class of c exchanged), the graph is isomorphic to the thesis graph,
and its diameter is ≥ 9 by Corollary 3.1 (reading 2: every q) and Corollary 4.1 (every reading, q ≥ 7).

*Proof.* Copy edges are preserved because g_c is an automorphism of I; hub edges are carried along by definition. ∎

**Lemma 5.3 (Theorem; reduction).** Take a geometric labelling, with any pattern and inner classes.

(a) If q is not a power of 3, every hub class sits on one type in all copies it meets, all unbarred classes sit on the
same type, and all barred classes on the other: the inner classes are those of reading 2 or of its dual.
(b) If q is a power of 3, the graph is isomorphic to one with a geometric labelling in reading 2 (same pattern).
(c) In reading 2, the graph is isomorphic to one with P_c = P₀ for all c and L_c = λ_c L₀ with collineations λ_c (the
*normal form*); in the dual of reading 2, to one with P_c = P₀ and L_c = λ_c L₀ as well, the unbarred hubs now sitting
on lines. In both cases call the bar that sits on points the **point bar** 𝒫 and the other the **line bar** ℒ.

*Proof.* (a) A transfer from a copy where Y sits on points to one where it sits on lines maps P to L; an automorphism
of I doing that is a duality, which does not exist (Fact 1.2). In every copy the two unbarred classes sit on the same
type. The copies are linked by unbarred classes: inside a block the pairs {k ± 1} (type a) or {k + 3, k + 4} (type b),
k ∈ Z₅, form a 5-cycle on the positions, and every class meets every block. So all unbarred classes sit on one type;
barred classes sit on the other type in every copy.
(b) Fix a duality δ and relabel by δ every copy in which the unbarred classes sit on lines (Lemma 5.2). The new transfers
are the old ones composed with δ^{±1}, so they are still automorphisms of I, and now all unbarred classes sit on points.
(c) In reading 2 the transfers of unbarred classes are restrictions of collineations to P, and the unbarred classes link
all copies (as in (a)); fixing a copy c₀, every P_c P_{c₀}⁻¹ is a product of transfers, so P_c = a_c P_{c₀} with a
collineation a_c. In the same way (barred classes also link all copies: pairs {k + 2, k + 3} and {k ± 1}),
L_c = b_c L_{c₀}. Relabel copy c by a_c⁻¹ (Lemma 5.2): P_c becomes P_{c₀} and L_c becomes a_c⁻¹b_c L_{c₀}. Unbarred
rows and barred rows are different vertices, so renaming the unbarred rows by P₀⁻¹P_{c₀} and the barred rows by
L₀⁻¹L_{c₀} gives P_c = P₀ and L_c = λ_c L₀ with λ_c = a_c⁻¹b_c. The dual reading is the same with the bars exchanged. ∎

From now on: normal form, rows of the point bar identified with points by P₀ (so the hub (t, X), X ∈ 𝒫, is adjacent to
point t of every copy in C(X)), and collineations λ_c acting on P and on L.

### 5.2 Routes reach balls

For X ∈ 𝒫 and c′ ∉ C(X), let N(X, c′) be the set of copies c₁ ∈ C(X) such that some class of ℒ meets both c₁ and c′.

**Lemma 5.4 (Theorem; routes).** Let X ∈ 𝒫, c′ ∉ C(X) and t ∈ P. Every point v of copy c′ with
d((t, X), (c′, v)) ≤ 7 lies in

  B(t, 4) ∪ ⋃_{c₁ ∈ N(X,c′)} B(λ_{c′}λ_{c₁}⁻¹(t), 4) ∪ ⋃_{(c, d) ∈ W₂} B(λ_cλ_d⁻¹(t), 2),

where W₂ is the set of ordered pairs of distinct copies of the following three kinds (all classes of ℒ unless said):
(c′, c₂) with c₂ sharing a class of 𝒫 with some c₁ ∈ C(X) and a class of ℒ with c′; (c′, c₁) with c₁ ∈ C(X) and some
c₂ sharing a class of ℒ with c₁ and with c′; (c₂, c₁) with c₁ ∈ C(X), c₂ sharing a class of ℒ with c₁ and a class of 𝒫
with c′.

*Proof.* A path from h = (t, X) to (c′, v) goes to point t of a copy c₁ ∈ C(X), then alternates walks inside copies (of
lengths a₁, …, a_r ≥ 0) with r − 1 passes copy → hub → copy, ending in c′. A hub meets each copy at most once, so
consecutive copies differ; c₁ ≠ c′, so r ≥ 2. The length is 1 + Σa_i + 2(r − 1) ≤ 7, so Σa_i ≤ 8 − 2r and r ≤ 4. A pass
through a 𝒫-hub happens at a point and keeps it (𝒫-hubs sit on the same point in every copy). A pass through an ℒ-hub
(m, Y) happens at a line and goes from λ_c L₀(m) in c to λ_d L₀(m) in d: it applies λ_dλ_c⁻¹. Collineations preserve
distances, so by induction the end lies in B(g(t), Σa_i), g the product of the maps applied. The walk starts and ends
at points; a segment before an ℒ-pass ends at a line, so the segments around ℒ-passes are odd and Σa_i is even.

- r = 2 (Σa_i ≤ 4): a 𝒫-pass gives g = id; an ℒ-pass needs a class of ℒ meeting c₁ and c′, i.e. c₁ ∈ N(X, c′), and
  gives g = λ_{c′}λ_{c₁}⁻¹.
- r = 3 (Σa_i ≤ 2): 𝒫 then 𝒫 gives id. 𝒫 then ℒ forces a₁ = 0, a₂ = a₃ = 1 and g = λ_{c′}λ_{c₂}⁻¹ (first kind). ℒ then
  𝒫 forces a₁ = a₂ = 1, a₃ = 0 and g = λ_{c₂}λ_{c₁}⁻¹ (third kind). ℒ then ℒ forces a₁ = a₃ = 1, a₂ = 0: both passes use
  the same row m, so g = λ_{c′}λ_{c₂}⁻¹λ_{c₂}λ_{c₁}⁻¹ = λ_{c′}λ_{c₁}⁻¹ (second kind).
- r = 4: all a_i = 0, so the walk never reaches a line, all passes are 𝒫-passes, and v = t. ∎

For a pair (X, c′) let r₄ = |N(X, c′)| and let m₂ be the number of pairs in W₂ that are not of the form (c′, c₁) with
c₁ ∈ N(X, c′). Different pairs may give the same map; counting pairs only overestimates. By Lemma 1.6, B(t, 4) misses
opp(t), every other radius-4 ball meets opp(t) in at most q⁴ points and every radius-2 ball in at most q². Hence:

**Corollary 5.5 (Theorem).** Every hub (t, X) has at least q⁵ − r₄q⁴ − m₂q² points of c′ at distance ≥ 9 (they are at
odd distance, since all points of all copies have one colour). Moreover m₂ ≤ (4α − 1) + 2α·2(2α − 1) = 8α² − 1: the
first two kinds are pairs (c′, b), at most 5α − 1 − r₄ of them besides those already counted in r₄, and the third kind
has ≤ 2α choices of c₁ and, since c₁ is met by two classes of ℒ that meet 2α copies each, ≤ 2(2α − 1) choices of c₂.

### 5.3 Starved pairs

Call (X, c′) with X ∈ 𝒫, c′ ∉ C(X) **starved** if r₄ = α, i.e. exactly one copy of C(X) per block shares a class of ℒ
with c′.

**Lemma 5.6 (Theorem).** For every block pattern there are starved pairs with X unbarred and starved pairs with X
barred:

- X = k unbarred: c′ = 5B′ + k + 3 for a block B′ of type a; if all blocks are of type b, c′ = 5B′ + k.
- X = k̄ barred: c′ = 5B′ + k + 3 for a block B′ of type b; if all blocks are of type a, c′ = 5B′ + k + 1.

*Proof.* The classes meeting the copy at position i are: in an a-block, unbarred i ± 1 and barred i + 2, i + 3; in a
b-block, unbarred i + 1, i + 2 and barred i ± 1. For X = k (ℒ = barred), c′ at position k + 3 of an a-block has barred
classes {k, k + 1}. In an a-block, C(k) has positions k − 1 (barred {k + 1, k + 2}: shares) and k + 1 (barred
{k + 3, k + 4}: does not). In a b-block, C(k) has positions k + 3 (barred {k + 2, k + 4}: no) and k + 4 (barred
{k, k + 3}: shares). If all blocks are b, c′ at position k has barred {k − 1, k + 1}; C(k) has k + 3 (barred {k + 2, k + 4}:
shares k + 4 = k − 1) and k + 4 (barred {k, k + 3}: no). For X = k̄ (ℒ = unbarred), c′ at position k + 3 of a b-block has
unbarred {k + 4, k}. In an a-block C(k̄) has k + 2 (unbarred {k + 1, k + 3}: no) and k + 3 (unbarred {k + 2, k + 4}:
shares); in a b-block, k − 1 (unbarred {k, k + 1}: shares) and k + 1 (unbarred {k + 2, k + 3}: no). If all blocks are a,
c′ at position k + 1 has unbarred {k, k + 2}; C(k̄) has k + 2 (unbarred {k + 1, k + 3}: no) and k + 3 (unbarred {k + 2, k + 4}:
shares). In each case c′ ∉ C(X). ∎

**Computer-checked C4 (route words).** For α = 5, 6, 7, 8 and every block pattern (by block swaps only the number of
a-blocks matters), the routes of Lemma 5.4 were enumerated for every pair (X, c′):

- every pair has r₄ ≥ α, and no route ends in a radius-0 ball other than the identity;
- for α = 5 (q = 7, 8), every starved pair, of either bar and in every pattern, has m₂ ≤ 140;
- for α = 6 (q = 9), every starved pair has m₂ ≤ 201;
- the best starved pair of the worst pattern has m₂ = 134 (α = 5, patterns aabbb, aaabb), 197 (α = 6, aaabbb),
  262 (α = 7, aaabbbb), 347 (α = 8, aaaabbbb).

Twice for the last item (`routecount.c` and `routecount2.c` of the relabelling note; `myroutes.py`/`sweep.py` of its
referee, which enumerates walks symbolically and does not use Lemma 5.4's families); the first three items by the
referee's enumerator, re-run for this note (`starved.py`, log `research/theorems/omega_note/logs/starved_alpha5_6.txt`).

### 5.4 q ≥ 8

**Theorem 3 (computer-assisted for q = 8, 9).** Let q ≥ 8. For every block pattern, every choice of inner classes
(both readings, their duals, or any choice per copy) and every geometric labelling, ΩH_q has diameter ≥ 9. More
precisely, in the normal form, for every starved pair (X, c′) every hub (t, X) has at least q⁵ − αq⁴ − m₂q² > 0
vertices of c′ at distance ≥ 9.

*Proof.* By Lemma 5.3 we may assume the normal form, in reading 2 or its dual. Take a starved pair of the point bar
(Lemma 5.6) and apply Corollary 5.5 with r₄ = α. For q ≥ 10, m₂ ≤ 8α² − 1 and the bound is positive when
q²(q − α) ≥ 8α²; with α ≤ (q + 3)/2 it suffices that q²(q − 3) ≥ 4(q + 3)², i.e. q³ − 7q² − 24q − 36 ≥ 0, which holds at
q = 10 (value 24) and for larger q (the derivative 3q² − 14q − 24 is positive). For q = 8 (α = 5), C4 gives m₂ ≤ 140 and
the bound is ≥ 32,768 − 20,480 − 8,960 = 3,328; for q = 9 (α = 6), m₂ ≤ 201 and the bound is
≥ 59,049 − 39,366 − 16,281 = 3,402. ∎

| q | α | far vertices per hub of a starved class, by hand (m₂ ≤ 8α² − 1) | best pair of the worst pattern (C4) |
|---:|---:|---:|---:|
| 8 | 5 | — (uses C4: ≥ 3,328 for every starved pair) | 3,712 |
| 9 | 6 | — (uses C4: ≥ 3,402 for every starved pair) | 3,726 |
| 11 | 7 | ≥ 11,253 | 26,862 |
| 13 | 8 | ≥ 56,446 | 84,162 |

This covers (11,8), (12,8), (14,8), (15,8), (16,8). Summing over all starved pairs (different pairs give disjoint sets of
(hub, vertex) pairs), every geometric labelling leaves at least 3.33·10⁹ far pairs at q = 8 and 7.43·10⁹ at q = 9
(Computer-checked twice: relabelling note and its referee, `logs/total_far_bounds_q8_q9.txt`).

The relabelling note first proved the other readings separately for q = 8, 9, 11, 13 and 27 (its Theorem 3.5). Its
referee observed that Lemma 5.3(b) reduces them to reading 2 for every q, which is how they are handled here.

### 5.5 q = 7

At q = 7 the bound of Corollary 5.5 is negative (16,807 − 5·2,401 − 140·49 = −2,058), so the overlaps of the five
radius-4 balls must be used. Here q is odd and b is nondegenerate; 7 is prime and not a power of 3, so (Fact 1.2,
Lemma 5.3(a)) the collineations are elements of G₂(7) ≤ SO(7, 7) and the reading is reading 2 or its dual. Fix a starved
pair (X, c′) of the point bar (Lemma 5.6) and write g₁, …, g₅ for the elements λ_{c′}λ_{c_i}⁻¹, c_i ∈ N(X, c′), and
y_i = g_i(t). By Lemma 1.5, B(y, 4) ∩ P = y^⊥ ∩ Q(6, q) for a point y, so with C_i := y_i^⊥ ∩ opp(t) the points of c′
within distance 7 of (t, X) that are opposite t lie in C₁ ∪ … ∪ C₅ and in at most m₂ ≤ 140 balls of radius 2.

**Lemma 5.7 (Theorem; overlaps, q odd).** Let y, y′, t be distinct points of Q(6, q).
(a) If y ⊥ y′ and t lies on the line yy′, then y^⊥ ∩ y′^⊥ ∩ opp(t) = ∅. Otherwise t is not on the line yy′ and
|y^⊥ ∩ y′^⊥ ∩ opp(t)| ≥ q³ − q.
(b) If y, y′, y″ are points not on one line, |y^⊥ ∩ y′^⊥ ∩ y″^⊥ ∩ Q(6, q)| ≤ (q + 1)².
(c) If y, y′, y″ lie on one totally singular line ℓ not through t, all the pairwise and triple intersections of
y^⊥ ∩ opp(t), y′^⊥ ∩ opp(t), y″^⊥ ∩ opp(t) equal X_ℓ := ℓ^⊥ ∩ opp(t), and |X_ℓ| ≥ q³ − q.

*Proof.* If y ⊥ y′, the line yy′ is totally singular; if t is on it, y^⊥ ∩ y′^⊥ = (yy′)^⊥ ⊆ t^⊥. If y, y′ are not
perpendicular, the line yy′ meets Q(6, q) only in y, y′, so t is not on it. In both remaining cases y^⊥ ∩ y′^⊥ is the
perp of a line, a 5-dimensional space: a parabolic Q(4, q) (if y ̸⊥ y′) or a cone with vertex the line yy′ over a conic
(if y ⊥ y′); both have q³ + q² + q + 1 points. Its points not opposite t are those of Π^⊥, Π = ⟨y, y′, t⟩ a plane. For
three independent singular vectors spanning Π the Gram matrix of b has zero diagonal, so its rank is 3, 2 or 0 (a
symmetric matrix with zero diagonal and rank 1 would be vvᵀ with all v_i² = 0). The radical of Π^⊥ is Π ∩ Π^⊥, of
dimension 0, 1 or 3. In the first case Π^⊥ (dimension 4) carries a nondegenerate form with (q + 1)² or q² + 1 singular
points; in the second it is a cone over a conic, q² + q + 1 points; in the third Π is totally singular and
Π^⊥ = Π ⊕ ⟨w⟩ with Q(w) ≠ 0 (Q(6, q) has no totally singular 4-space), so its singular points are those of Π,
q² + q + 1. So |Π^⊥ ∩ Q(6, q)| ≤ (q + 1)², which gives (a) and, with Π = ⟨y, y′, y″⟩, (b). (c): y^⊥ ∩ y′^⊥ = ℓ^⊥ ⊆ y″^⊥,
and |X_ℓ| ≥ q³ − q by (a). ∎

**Lemma 5.8 (Theorem; coincidences).** If two of t, y₁, …, y₅ coincide, the hub (t, X) has at least
q⁵ − 4q⁴ − 140q² = 16,807 − 9,604 − 6,860 = 343 vertices of c′ at distance ≥ 9 (uses m₂ ≤ 140 from C4).

*Proof.* At most four distinct centres other than t remain; Corollary 5.5. ∎

Now let t, y₁, …, y₅ be distinct. Call y_i, y_j **aligned** if they lie on one totally singular line through t (then
C_i ∩ C_j = ∅ by Lemma 5.7(a)); the aligned classes partition {y₁, …, y₅}. Call a set of at least three y_i lying on one
line of PG(6, q) not through t, and maximal with this property, a **rich line**. Three collinear singular points span a
totally singular line, so every collinear triple of y's is inside an aligned class or a rich line; a rich line meets
each aligned class at most once, and two rich lines share at most one point.

**Lemma 5.9 (Theorem; the configuration types at q = 7).** Let A be the number of aligned pairs, T the number of
triples meeting three different aligned classes, and R₃ = Σ C(m, 3) over the rich lines (m points each). Then

  |C₁ ∪ … ∪ C₅| ≤ U := 5q⁴ − (10 − A − R₃)(q³ − q) + (T − R₃)(q + 1)²,

except when one rich line holds all five points, where U := 5q⁴ − 4(q³ − q). Up to relabelling there are exactly 17
configuration types; for q = 7 they are:

| aligned classes | rich lines | A | T | R₃ | U | F = 16,807 − U − 6,860 | forced ⊥ pairs p |
|---|---|---:|---:|---:|---:|---:|---:|
| 5 | — | 10 | 0 | 0 | 12,005 | −2,058 | 15 |
| 4, 1 | — | 6 | 0 | 0 | 10,661 | −714 | 10 |
| 3, 2 | — | 4 | 0 | 0 | 9,989 | −42 | 9 |
| 3, 1, 1 | — | 3 | 3 | 0 | 9,845 | 102 | 6 |
| 3, 1, 1 | 3 | 3 | 3 | 1 | 10,117 | −170 | 9 |
| 2, 2, 1 | — | 2 | 4 | 0 | 9,573 | 374 | 6 |
| 2, 2, 1 | 3 | 2 | 4 | 1 | 9,845 | 102 | 9 |
| 2, 2, 1 | 3, 3 | 2 | 4 | 2 | 10,117 | −170 | 12 |
| 2, 1, 1, 1 | — | 1 | 7 | 0 | 9,429 | 518 | 3 |
| 2, 1, 1, 1 | 3 | 1 | 7 | 1 | 9,701 | 246 | 6 |
| 2, 1, 1, 1 | 3, 3 | 1 | 7 | 2 | 9,973 | −26 | 9 |
| 2, 1, 1, 1 | 4 | 1 | 7 | 4 | 10,517 | −570 | 9 |
| 1, 1, 1, 1, 1 | — | 0 | 10 | 0 | 9,285 | 662 | 0 |
| 1, 1, 1, 1, 1 | 3 | 0 | 10 | 1 | 9,557 | 390 | 3 |
| 1, 1, 1, 1, 1 | 3, 3 | 0 | 10 | 2 | 9,829 | 118 | 6 |
| 1, 1, 1, 1, 1 | 4 | 0 | 10 | 4 | 10,373 | −426 | 6 |
| 1, 1, 1, 1, 1 | 5 | 0 | 10 | 10 | 10,661 | −714 | 10 |

Here p = Σ (s + C(s, 2)) over aligned classes of size s ≥ 2, plus Σ C(m, 2) over rich lines: the pairs among
{t, y₁, …, y₅} that every configuration of the type has perpendicular. In the 9 types with F ≤ 0, p ≥ 6.

*Proof.* |C_i| = q⁴ (Lemma 1.6, y_i ≠ t). Bonferroni: |⋃C_i| ≤ S₁ − S₂ + S₃, S_k the sum of the k-fold intersections.
By Lemma 5.7: an aligned pair contributes 0 to S₂ and every triple containing one contributes 0 to S₃; a pair inside a
rich line ℓ contributes |X_ℓ| and so does a triple inside it; every other pair contributes ≥ q³ − q, and every other
triple (it is not collinear) ≤ (q + 1)². A rich line with m ∈ {3, 4} points contributes −(C(m, 2) − C(m, 3))|X_ℓ| =
−2|X_ℓ| ≤ −2(q³ − q). Collecting terms gives U. If all five points lie on one rich line, all pairwise intersections
equal X_ℓ, so |⋃C_i| = 5q⁴ − 4|X_ℓ| exactly. The types: two 3-subsets of a 5-set sharing at most one point share exactly
one, a third 3-subset would share two points with one of them, and a 4- or 5-point rich line leaves no room for another.
So the rich-line systems are: none, one 3-line, two 3-lines through a common point, one 4-line, one 5-line. A rich line
takes at most one point from each aligned class, which leaves exactly the 17 rows above (partitions 5, 41, 32 admit no
rich line; 311: none or one 3-line; 221: none, one, or two 3-lines through the singleton; 2111: none, 3, 3+3, 4; 11111:
none, 3, 3+3, 4, 5). The numbers A, T, R₃ and p depend only on the row. ∎

(The table was also produced by three programs: `degen.py` of the relabelling note, `mytypes.py` of its referee, and
`types43.py` written for this note, `logs/types43_q7.txt`. The referee also built 2,500 explicit configurations in Q(6,7)
and found no union above its type's bound.)

**Lemma 5.10 (Theorem; few points are moved to perpendicular points).** Let q be odd with 3 | q − 1 and let h ∈ G₂(q)
fix no point of Q(6, q). Then Perp(h) := {s ∈ P : h(s) ⊥ s} has at most
(q⁵ − 1)/(q − 1) + q^{3.5} + q³ + (q − 2)q^{1.5} points: at most 4,144 of the 19,608 points of H(7).

*Proof.* Count N_h := #{v ∈ V : Q(v) = 0, F(v) = 0}, F(v) := b(v, hv); then |Perp(h)| = (N_h − 1)/(q − 1). F is a quadratic
form with polar form b(v, (h + h⁻¹)w), since b(w, hv) = b(h⁻¹w, v). With ψ a nontrivial additive character of F_q,
N_h = q⁻² Σ_{a,b ∈ F_q} Σ_{v ∈ V} ψ(aQ(v) + bF(v)). The terms with b = 0 give q⁻² · q · q⁶ = q⁵ (Q has q⁶ zeros). For b ≠ 0,
aQ + bF = b(F − cQ) with c = −a/b, and for fixed b, c runs over F_q. The form R_c = F − cQ has polar form
b(v, (h + h⁻¹ − c)w), so its rank is 7 − d_c with d_c = dim ker(h + h⁻¹ − c) = dim ker(h² − ch + 1). For a quadratic form
of rank r on F_q⁷ (q odd), |Σ_v ψ(R(v))| = q^{7 − r/2} (diagonalize; each nonzero coefficient gives a Gauss sum of absolute
value q^{1/2}). Hence |N_h − q⁵| ≤ (q − 1) Σ_{c ∈ F_q} q^{1.5 + d_c/2}, and |Perp(h)| ≤ (q⁵ − 1)/(q − 1) + q^{1.5} Σ_c q^{d_c/2}.

For c ≠ c′ the polynomials x² − cx + 1 and x² − c′x + 1 are coprime (their difference is (c′ − c)x, and x divides
neither), so the kernels are independent and Σ_c d_c ≤ 7. Each d_c ≤ 4:
(i) if x² − cx + 1 = (x − μ)(x − μ⁻¹) with μ ∈ F_q, μ ≠ ±1, the kernel is ker(h − μ) ⊕ ker(h − μ⁻¹); an eigenvector v
with hv = μv has Q(v) = Q(hv) = μ²Q(v), so Q(v) = 0 and ⟨v⟩ is a fixed point. So d_c = 0.
(ii) c = ±2: ker(h ∓ 1) contains no singular vector (it would give a fixed point), so it has dimension ≤ 2 (a quadratic
form in ≥ 3 variables over F_q has a nontrivial zero, by Chevalley–Warning), and dim ker(h ∓ 1)² ≤ 2 dim ker(h ∓ 1) ≤ 4.
(iii) if x² − cx + 1 is irreducible with roots μ, μ^q = μ⁻¹ in F_{q²}, then d_c = 2 dim ker(h − μ) (over F_{q²}) ≤ 2m(μ),
m(μ) the multiplicity of μ as a root of the characteristic polynomial. By Fact 1.3 the roots are 1, x₁^{±1}, x₂^{±1},
x₃^{±1} with x₁x₂x₃ = 1. Since μ ≠ μ⁻¹, μ occurs at most once for each index, so m(μ) ≥ 3 means μ = x₁^{ε₁} = x₂^{ε₂} =
x₃^{ε₃}, hence μ^{ε₁+ε₂+ε₃} = 1 with ε₁ + ε₂ + ε₃ ∈ {±1, ±3}; μ ≠ 1 forces μ³ = 1, and since 3 | q − 1 the cube roots of
unity lie in F_q, contradicting irreducibility. So m(μ) ≤ 2 and d_c ≤ 4.
The function d ↦ q^{d/2} is increasing and convex; for integers 0 ≤ d_c ≤ 4 with Σd_c ≤ 7, moving one unit from a smaller
entry to a larger one (below 4), or raising an entry, does not decrease Σ q^{d_c/2}, so the maximum is at (4, 3, 0, …, 0):
q² + q^{1.5} + (q − 2). This gives the bound. At q = 7: 2,801 + 907.5 + 343 + 92.6 = 4,144.1. ∎

(Sampled: |Perp(h)| ∈ {2,752, 2,850} for 229 and for 224 fixed-point-free elements of G₂(7), in two separate samples;
`logs/fpfperp_q7.txt` of the relabelling note, `logs/lemma44_sampling_q7.txt` of its referee.)

**Theorem 4 (computer-assisted: uses m₂ ≤ 140 from C4).** For q = 7, every block pattern, every choice of inner classes
and every geometric labelling, ΩH₇ has diameter ≥ 9.

*Proof.* By Lemma 5.3(a), (c) we have reading 2 or its dual in normal form; take a starved pair (X, c′) of the point bar
(Lemma 5.6) and suppose that every hub of X is within distance 8 of every point of c′. Consider the 15 elements g_i
(1 ≤ i ≤ 5) and g_i⁻¹g_j (i < j) of G₂(7). If one of them fixes a point t, then two of t, y₁(t), …, y₅(t) coincide
(g_i(t) = t, or g_i(t) = g_j(t)), and Lemma 5.8 gives a far vertex. So none of them has a fixed point. Then for every
point t the six points t, y₁, …, y₅ are distinct, and by Lemma 5.9 and Corollary 5.5 (far vertices ≥ F) the configuration
at t is of one of the 9 types with F ≤ 0, so at least 6 of the 15 pairs among t, y₁, …, y₅ are perpendicular. The pair
(t, y_i) is perpendicular iff t ∈ Perp(g_i), and (y_i, y_j) iff t ∈ Perp(g_i⁻¹g_j), since collineations preserve ⊥.
Summing over the 19,608 points t: Σ_h |Perp(h)| ≥ 6 · 19,608 = 117,648 over the 15 elements h, while Lemma 5.10
(q = 7, 3 | 6) gives Σ_h |Perp(h)| ≤ 15 · 4,144 = 62,160. Contradiction. ∎

**Corollary 5.11 (Theorem; computer-assisted at q = 7, 8, 9).** For every table value of ΩH_q, (10,8) 1,176,480,
(11,8) 2,246,940, (12,8) 4,650,100, (14,8) and (15,8) 14,172,480 and (16,8) 36,201,060, no geometric labelling of the
copies gives diameter 8, under any reading of Figs. 2.21a/b, any choice of inner classes and any mix of block types.
For (14,8), (15,8) and (16,8) the proof is entirely by hand.

**Computer-checked C5 (consistency).** On explicit graphs with random collineation labellings (a_c, b_c independent),
BFS from a hub of a starved class reaches exactly the union of the balls predicted by the route words, and gives
(referee of the relabelling note, `omg.c`, `driver.py`):

| q | graph | far points in c′ (BFS) | proved lower bound | hub eccentricity |
|---:|---|---:|---:|---:|
| 7 | ΩH₇ aabbb, 1,176,480 vertices | 5,221 | > 0 (Theorem 4) | 9 |
| 8 | ΩH₈ aabbb, 2,246,940 vertices | 12,943 | 3,712 | 9 |
| 9 | ΩH₉ aaabbb, 4,650,100 vertices | 22,158 | 3,726 | 9 |

With a_c = b_c the distance profile from a hub equals that of the thesis graph (Lemma 5.2).

## 6. What remains open

1. **Arbitrary labellings (q ≥ 4).** Whether some non-geometric labelling of Gómez's wiring gives diameter 8 at
   q = 7, 8, 9, 11, 13 is open. By Corollary 5.11 it would have to be non-geometric. Counting does not exclude it: the
   most a hub's routes can cover, summed over routes, is 9.4n (q = 3), 5.5n (4), 5.6n (5), 4.3n (7), 3.7n (9) and
   3.1n (13), n the number of targets in the copy (table audit, `ubound.py`), so the union bound stays near 3 as q
   grows. When a transfer is not geometric, the three terms of a route (walks of length 0, 2, 4 before the pass) can
   each contribute about q⁴ targets instead of collapsing to one ball; a repair would need transfers that scatter the
   radius-2 and radius-4 balls almost perfectly and fit together across hubs.

   *Computer-checked C6 (searches).* No labelling with diameter 8 was found at q = 4 (54,600 vertices) or q = 5
   (195,300): annealing with a Singer-type symmetry and eight squad variants ended at about 12,000–13,900 far pairs from
   390 hub representatives (q = 4) and 35,500–38,000 from 252 (q = 5) (table audit, round 2). At q = 7 a random
   labelling with the Singer-cube symmetry leaves 6,813,773 far pairs from 2,064 hub representatives. Mean far-pair
   counts of uniformly random labellings: about 70 (q = 2), 1,911 (3), 645,753 (4), 6.55·10⁶ (5), 6.5·10⁸ (7). Geometric
   labellings are much worse than random ones at every q tested: annealed collineation labellings leave 805 (q = 2),
   259,169 (3), 18.2·10⁶ (4) and 209·10⁶ (5) far pairs.

   *Heuristic H1 (first moment).* If the far pairs of a uniformly random labelling were independent events, the expected
   number of labellings with diameter 8 would be exp(ln #labellings − E[F]), with #labellings = (N!)^{10α−1} up to a
   global renaming: e^{+3.7·10³} at q = 2, e^{+5.0·10⁴} at q = 3, e^{−4.0·10⁵} at q = 4, e^{−5.4·10⁶} at q = 5,
   e^{−6.4·10⁸} at q = 7. The gap: far pairs are strongly dependent, and the estimate says nothing about structured
   labellings.

2. **Labellings per (hub class, copy).** If the two classes of one bar meeting a copy may use different bijections, the
   model of §5.1 does not apply, even when every transfer is a collineation. The counting method fails there for every
   q: every copy met by X shares a class with c′, so there are at least 2α ≥ q + 2 distinct radius-4 centres (at q = 8:
   10 radius-4 and 318 radius-2 centres, bound −24,448; at q = 13: 16 and 864, bound −203,138; Computer-checked once,
   `logs/perclass.txt` of the referee). Open.

3. **Other wirings.** *Heuristic H2.* Theorems 3 and 4 use the starved pairs of Gómez's wiring, where only α ≈ q/2 copies
   reach c′ in one pass. A wiring giving every pair about q + 3 one-pass routes is not excluded by size. A near-exact
   cover would need about q of the centres on one totally singular line through t for every t (Lemma 5.7: centres in
   general position overlap in about q³ points), which points to long root elations x ↦ x + b(x, u)v − b(x, v)u (u, v
   spanning a hexagon line); a root group moves t only along one line and has fixed points, which Lemma 5.8 penalises.
   The gaps: "near-exact cover ⇒ line structure" and "line structure for all t ⇒ one root group" are not proved.

4. **q ≤ 5 in the geometric class** (not table values). Neither the count of Theorem 3 nor the q = 7 argument works:
   the general-position bound is −357 at q = 4 and −1,024 at q = 5, and Lemma 5.10 needs 3 | q − 1, false at q = 5. There
   are only the measurements of C6. The subclass a_c = b_c (Lemma 5.2) is settled for every q.

5. **The relabelled graphs at q = 2, 3.** *Computer-checked C7.* With arbitrary per-copy labellings found by annealing
   (table audit), ΩH₂ (pattern ab, 1,890 vertices, copy vertices of degree 5 and hubs of degree 4) and ΩH₃ (pattern
   aba, reading 1, 14,560 vertices, 6-regular) have diameter 8. ΩH₃: two labellings, equivariant under a Singer-type
   collineation of order 13, files `research/projects/table-audit/omega/labs/q3_aba_LLL_G13.lab` and
   `q3_aba_LLL_G13_Z5psi.lab` (branch claude/table-audit-2-p7x6hn); all-pairs BFS with no symmetry assumed and an
   independent wiring check (audit, `checks/omega_labelled.txt`), and a third rebuild with separate wiring and BFS code
   (referee omega-dq, `logs/audit_relabelled_q3.txt`). ΩH₂: one labelling, all-pairs BFS by the audit only
   (`checks/omega_D8.txt`); not re-checked independently. These graphs are far below the table at (5,8) and (6,8)
   (9,234 and 29,790); they only show that the claimed bound D₁ + 2 can hold for a suitable labelling at q ≤ 3. Their
   labellings have not been analysed: we do not know a description of them, and in particular whether any structure
   would extend to larger q.

## 7. The table entries: what can be claimed

| cell | value | as defined (thesis labelling) | geometric relabellings | arbitrary relabellings |
|---|---:|---|---|---|
| (10,8) | 1,176,480 = \|ΩH₇\| | diam ≥ 9 (Cor. 3.1, 4.1); = 9 computed (C2) | ≥ 9 (Thm 4, computer-assisted) | open |
| (11,8) | 2,246,940 = \|ΩH₈\| | ≥ 9; eccentricity 9 computed | ≥ 9 (Thm 3, computer-assisted) | open |
| (12,8) | 4,650,100 = \|ΩH₉\| | ≥ 9; = 9 computed | ≥ 9 (Thm 3, computer-assisted) | open |
| (14,8) | 14,172,480 = \|ΩH₁₁\| | ≥ 9; eccentricity 9 computed | ≥ 9 (Thm 3, by hand) | open |
| (15,8) | 14,172,480 = \|ΩH₁₁\| | ≥ 9; eccentricity 9 computed | ≥ 9 (Thm 3, by hand) | open |
| (16,8) | 36,201,060 = \|ΩH₁₃\| | ≥ 9; eccentricity 9 computed | ≥ 9 (Thm 3, by hand) | open |

**What can be claimed** (the two referees' recommended wording, combined):

> The table entries (10,8) 1,176,480, (11,8) 2,246,940, (12,8) 4,650,100, (14,8) 14,172,480, (15,8) 14,172,480 and
> (16,8) 36,201,060 are the orders of Gómez's graphs ΩH_q (thesis, UPC 1986, §2.9.3; q = 7, 8, 9, 11, 11, 13). The
> thesis claims diameter ≤ D₁ + 2 = 8 without proof. As defined there (every copy of the hexagon carries the same
> labels, and a copy of K₁ with label t is joined only to vertices labelled t), ΩH_q has diameter at least 9 for each of
> these q, under every reading of Figs. 2.21a/b and every pairing of point labels with line labels (proof: Theorems 1
> and 2; also checked by computation). The paper the table cites (Delorme, Gómez, Quisquater, "On large bipartite
> graphs") was never published, so these cells have no checkable graph of diameter 8.
>
> Give each copy of the hexagon its own labelling: a bijection from the rows to the points and one to the lines, used by
> every hub class of that colour that meets the copy. Call the labelling geometric if every transfer map between two
> copies met by one hub class is induced by an automorphism of the incidence graph of H(q) (a collineation, or a
> duality when q = 3^e). For every q ≥ 7, every geometric labelling gives diameter ≥ 9. This holds in every reading of
> Figs. 2.21a/b, for every choice of inner classes and every mix of block types. It covers all six table entries. For
> q ≥ 8 the proof is a ball-counting argument; it gives explicit numbers: some hub class X and missed copy c′ have at
> least q⁵ − αq⁴ − m₂q² vertices of c′ at distance ≥ 9 from every hub of X (3,712, 3,726, 26,862 and 84,162 at
> q = 8, 9, 11, 13). For q = 7 the proof adds Bonferroni inequalities and a character-sum bound on how many points a
> fixed-point-free element of G₂(7) moves to perpendicular points.

**What cannot be claimed.**

- That no (Δ, 8) graph of these orders exists. The cells have "no checkable graph of diameter 8", nothing more.
- That no relabelling of ΩH_q works. Arbitrary per-copy labellings are open for every q ≥ 4 (and work at q = 2, 3);
  labellings per (hub class, copy) are open; other wirings are open.
- Anything about q ≤ 5 in the geometric class beyond measurements.
- Anything about ΩH₁₁d (N(15,8) ≥ 14,978,080 in the thesis): it is not defined in §§2.7–2.9 and the table does not use it.
- The (13,8) entry 5,314,680 (also credited to Delorme–Gómez–Quisquater) is not in the thesis; nothing here bears on it.

**The lab's own graphs in these cells** do not depend on any of this: (11,8) 2,258,520 and (15,8) 18,128,880 are explicit
Haar graphs (README, independent checks), and the largest valid (12,8) graph we know is a Haar graph on
PSL(2, 67) × Z₁₃ with 3,909,048 vertices (branch claude/cell-12-8-search-qhi11t), below the table value.

## 8. Sources, programs and logs

All on github.com/dogaozden/degree-diameter, by branch.

- **Theorems 1, 2 and the thesis graphs**: `research/squads/cells/d12D8_table.md` and `research/d12D8/omega/`
  (`hexq6.c`, `omega.c`, `omega_bfs.c`, `apsp_auto.c`, `haut.py`, `omgens.py`, logs `hex_checks.txt`,
  `check_om9_r2.txt`, `check_om9_r1s.txt`, `thesis_values_bfs.txt`, `witness_pairs.txt`), branch
  claude/own-12-8-cell-ig5jhd (568fb4f).
- **Referee of Theorems 1, 2**: `research/referee/omega-dq.md` and `research/referee/omega-dq/` (`hexgen.c`, `hexgf.c`,
  `bitapsp.c`, `omegaref.c`, `omegacheck.py`, `omegalab.py`, `thm2_bound.py`, logs), branch claude/omega-dq-referee-bzzlid
  (b5db2bb).
- **Relabellings**: `research/theorems/OMEGA_REPAIR.md` and `research/omega_repair/` (`twist.c`, `routecount.c`,
  `routecount2.c`, `degen.py`, `perpbound.py`, `tanneal.c`, logs), branch claude/thm-omega-repair-m4luls (5f64a1d); its
  internal q = 7 referee report `research/omega_repair/referee/REPORT_q7.md`.
- **Referee of the relabellings**: `research/referee/omega-repair.md` and `research/referee/omega-repair/`
  (`buildhex.py`, `ghcheck.c`, `collin.py`, `myroutes.py`, `sweep.py`, `perclass.py`, `mytypes.py`, `e2e43.py`,
  `myperp44.py`, `omg.c`, `driver.py`, `drg.py`, logs), branch claude/referee-omega-repair-qt17fb (6337c85).
- **Table audit** (free relabellings at q = 2, 3; searches at q = 4, 5, 7; union bound; first moment):
  `research/projects/table-audit/AUDIT.md` §§4, 7, `research/projects/table-audit/omega/NOTES.md`, `omega/labs/`,
  `checks/omega_labelled.txt`, `checks/omega_D8.txt`, `checks/witness_omega_thesis.txt`, branch
  claude/table-audit-2-p7x6hn (e1fe451).
- **Lean**: `lean/BipartiteDD/LeanMaxx/Projection/{Walk,Main,Axioms}.lean`, `research/lean-maxx/STATUS-projection.md`,
  branch claude/leanmaxx-projection-r0kehl (50cc900); verification `research/lean-maxx/VERIFY.md`, branch
  claude/leanmaxx-verify-9ummw2 (2ff0c8e).
- **This note**: `research/theorems/OMEGA_NOTE.md`, `research/theorems/omega_note/` (`OMEGA_NOTE.tex`,
  `OMEGA_NOTE.pdf`, `starved.py`, `types43.py`, `typetable.py`, logs), branch claude/omega-d8-note-xrbqux. The checks
  re-run for this note: the Theorem 2 constants (`thm2_bound.py` of the referee), the route words for α = 5, 6
  (`starved.py`, using the referee's `myroutes.py`), and the q = 7 type table (`types43.py`, written from scratch).

## References

- [Gó86] J. Gómez Martí, *Diámetro y vulnerabilidad en redes de interconexión*, PhD thesis, Universitat Politècnica de
  Catalunya, Barcelona, 1986. Scan: web.mat.upc.edu/francesc.comellas/delta-d/papers/Gomez1986-PhD-red.pdf.
- [DGQ] C. Delorme, J. Gómez, J.-J. Quisquater, On large bipartite graphs, manuscript (cited as unpublished; not found).
- [MS13] M. Miller, J. Širáň, Moore graphs and beyond: a survey of the degree/diameter problem, Electron. J. Combin.
  (2013), dynamic survey DS14v2, Table 4.
- [CW] CombinatoricsWiki, The Degree Diameter Problem for Bipartite Graphs.
- [Ti59] J. Tits, Sur la trialité et certains groupes qui s'en déduisent, Publ. Math. IHÉS 2 (1959), 13–60.
- [VM98] H. Van Maldeghem, *Generalized Polygons*, Birkhäuser, 1998.
- [ÖD7] Degree–diameter lab, Bipartite graphs of diameter 7 from the split Cayley hexagon, draft of 25 October 2026
  (`papers/Ozden_D7_hexagon.pdf`).
