# Flag graphs of spherical buildings and the bipartite degree–diameter problem (thm-buildings, 2026-10-24)

Job "thm-buildings" (Opus). Branch `claude/buildings-flag-graph-diameter-g9lf1o`. This note finishes the sketch in
REGULARITIES.md §1.2 (branch `claude/theorem-search-regularities-nt0d98`). Every claim has a script in
`research/theorems/buildings/` and a saved output in `research/theorems/buildings/out/`. "Table" means the 2013
bipartite table (DS14v2 Table 4 = research/frontier/TABLE.md). "Ours" means the largest value in research/frontier/TABLE.md
or research/RESULTS.md. The literature search was a Haiku squad round, logged in research/squads/LOG.md, with notes in
research/squads/buildings-r1-lit/.

n_b(Δ, D) is the largest order of a bipartite graph with maximum degree ≤ Δ and diameter ≤ D, and
M_b(Δ, D) = 2(1 + (Δ−1) + … + (Δ−1)^(D−1)) is the bipartite Moore bound.

## Short answer

1. **Proved, all types: the bipartite flag graph of a spherical building has diameter exactly the Coxeter number h**
   (Theorem 1, §1.3). The proof is now complete. The sketch had a real gap: it turned a factorisation of the Weyl
   distance into a path without checking that the lengths add. The proof also needed a lower bound for every type,
   not only the computed ones. Both are fixed. The exact distance between any two vertices is a function of their
   Weyl distance (Theorem 2). So every vertex on one side has the same number of vertices at each distance, with no
   symmetry assumed. That formula was checked against breadth-first search, layer by layer, on 21 buildings: types
   A₂–A₅, B₂–B₄/C₂–C₄ and D₄, over GF(2), GF(3), GF(4), including six with unequal parameters (Hermitian and elliptic
   polar spaces). All 21 also pass the coordinator's all-pairs checker. Pairs from opposite chambers were tested
   directly in 12 geometries.
2. **The asymptotic statement is true for every D ≥ 2, not only for odd D, D ≡ 0 mod 4 and D = 6, 12, 30. But it
   follows in one line from a theorem published in August 2026.** Cames van Batenburg–Korsky (arXiv:2608.03965) prove
   lim n(Δ, D)/Δ^D = 1 for general graphs and every D. The doubling n_b(Δ, D) ≥ 2·n(Δ−1, D−1) (REGULARITIES §1.4,
   which they also use, for edges) turns this into lim n_b(Δ, D)/M_b(Δ, D) = 1 for every D. Nobody states the
   bipartite version. The 2013 survey (DS14v2, p. 36) says it was known only for D = 2, 3, 4, 6. CvB–K's only
   bipartite limit, in the paper and in their Lean README, is for the edge version; Isham et al. treat general graphs
   only. So it is a corollary to record, not a new theorem (§1.9).
3. **"D ≡ 2 mod 4 is not reached by buildings" is false.** Delorme's 1985 product G ⊗ Opp(G) of any flag graph is
   regular of degree ∏(q_s + 1), with diameter exactly h and order/M_b → 1 (Theorem 3). This works for unbalanced
   diagrams too, so every h ≥ 3 is reached, for example by A_{h−1}(q) or B_{h/2}(q).
4. **What buildings add beyond 2026: much faster convergence.** The deficiency 1 − n/M_b is c/q + O(q⁻²) with an
   explicit c (Theorem 4, all constants checked numerically). In terms of the degree it is c·Δ^(−α), with α as below.

   | D | route | α |
   |---|---|---|
   | odd | A_{D−1} | 2/(D−1) |
   | ≡ 0 mod 4 | Sp(D, q) | 4/D |
   | 12 | F₄ | 1/2 |
   | 30 | E₈ | 1/4 |
   | ≡ 2 mod 4 | Delorme product of B_{D/2} | 2/D |
   | any | doubled CvB–K | 1/(2D−2) |

   At D = 5, A₄(q) reaches 50 % of the Moore bound at Δ = 81 and 90 % at Δ = 3,600. Doubled CvB–K is still under
   25 % at Δ ≈ 6.5·10⁹. Delorme's quotient of the same graphs also gives general graphs of every diameter with ratio → 1
   and a faster rate than CvB–K (§1.7(f)), a side remark.
5. **Table cells.** Only (16,5) is above the 2013 table: A₄(3) with 31,460 > 27,300. That graph is CvB–K's, and our
   33,792 is larger. Nothing derived from buildings beats our best value in any cell with Δ ≤ 16, D ≤ 10 (§1.8). The
   closest are:

   | graph | cell | share of our best |
   |---|---|---|
   | GQ(q−1, q+1) at q = 13, 11, 9 | (15,4), (13,4), (11,4) | 0.91–0.93 |
   | A₄(3) | (16,5) | 0.93 |
   | A₄(2) | (9,5) | 0.82 |
   | octagon product GO(2,4) ⊗ Opp | (15,8) | 0.57 |
   | C₄(3) | (16,8) | 0.66 of the table |

   GQ(q−1, q+1) is the AS(q) quadrangle that our Theorem A completes. In the table range every flag graph of a
   building of rank ≥ 3 is at most 0.29 of the Moore bound.

---

## 1. Proved

### 1.1 Setting

(W, S) is a finite irreducible Coxeter system of rank r ≥ 2, with length function ℓ, longest element w₀, N = ℓ(w₀)
and Coxeter number h. Then N = rh/2 (Bourbaki, *Lie*, Ch. V §6; checked for every type in `coxeter_check.py`). The
Coxeter diagram is a tree, so its vertices split into two colour classes I₁, I₂ with no edge inside a class. Two
generators in the same class therefore commute. So W_I ≅ (Z/2)^|I| for I ∈ {I₁, I₂}, and its elements are the
products ∏_{s∈T} s for T ⊆ I, of length |T|. For a class J, J′ is the other class. c_J = ∏_{s∈J} s.

A building of type (W, S) is a set 𝒞 of chambers with a Weyl distance δ: 𝒞 × 𝒞 → W satisfying (Abramenko–Brown,
*Buildings*, GTM 248, Def. 5.1):
- (WD1) δ(C, D) = 1 iff C = D;
- (WD2) if δ(C, D) = w and δ(C′, C) = s ∈ S, then δ(C′, D) ∈ {sw, w}, and δ(C′, D) = sw when ℓ(sw) = ℓ(w) + 1;
- (WD3) if δ(C, D) = w, then for every s ∈ S there is C′ with δ(C′, C) = s and δ(C′, D) = sw.

The J-residue of C is R_J(C) = {D : δ(C, D) ∈ W_J}; its type is J. A panel is a residue of type {s}. If every s-panel
has q_s + 1 chambers, the q_s are the parameters, and q_w = ∏ q_{s_i} over any reduced word s₁⋯s_k of w. Finite
thick buildings of irreducible type and rank ≥ 2 have parameters; the ones that exist are listed in §1.5. Theorems 1
and 2 below use neither thickness nor finiteness.

**The graph Γ.** Its vertices are the I₁-residues and the I₂-residues. An I₁-residue R and an I₂-residue R′ are
adjacent iff R ∩ R′ ≠ ∅. In flag language, a residue of type J is the set of chambers containing a partial flag of
type S∖J. So the vertices are the partial flags of type I₂ and of type I₁, adjacent iff together they form a chamber.
For PG(n, q), a chamber is a complete flag; one side is its odd-dimensional members, the other its even-dimensional
members. For n = 2k this is CvB–K's "bipartite compatibility graph", which Isham et al. call C(k, q).

### 1.2 Facts used

Coxeter groups:
- (C1) Both alternating words c_{I₁} c_{I₂} c_{I₁} ⋯ and c_{I₂} c_{I₁} c_{I₂} ⋯, with h blocks each, are reduced
  words for w₀. Source: Fomin–Zelevinsky, "Y-systems and generalized associahedra", Ann. of Math. 158 (2003),
  Lemma 2.1 (arXiv hep-th/0111053, p. 9, read). It cites Bourbaki, *Lie*, Ch. V §6, Ex. 2. Also checked by computer
  for every irreducible type of rank ≤ 10, E₆–E₈, F₄, G₂, H₃, H₄ and I₂(m) for m ≤ 12 (`coxeter_check.py` →
  `out/coxeter_check.txt`: both words have N letters and every inversion root is positive).
- (C2) Subword property: if v = s₁⋯s_k is reduced and u ≤ v in Bruhat order, some subword of s₁⋯s_k is a reduced
  word for u (Björner–Brenti, *Combinatorics of Coxeter Groups*, Thm 2.2.2). Every u satisfies u ≤ w₀.
- (C3) Deletion condition: a non-reduced word has two letters whose removal does not change the product (Humphreys,
  *Reflection Groups and Coxeter Groups*, §5.8). Applying it repeatedly, the product of any subword of a word f is
  also the product of a reduced subword of f.
- (C4) W_J ∩ W_K = W_{J∩K} (Bourbaki, *Lie*, Ch. IV §1.8, Thm 2). In particular W_{I₁} ∩ W_{I₂} = {1}.

Buildings. All of these are standard (Abramenko–Brown, Ch. 5); each follows from (WD1)–(WD3) in a few lines:
- (B1) δ(D, C) = δ(C, D)⁻¹.
- (B2) *Galleries of reduced type.* If δ(C, D) = w and s₁⋯s_k is a reduced word for w, there are chambers
  C = C₀, C₁, …, C_k = D with δ(C_{i−1}, C_i) = s_i. Then δ(C_i, C_j) = s_{i+1}⋯s_j for i < j.
  *Proof.* Existence, by induction on k: (WD3) with s = s₁ gives C₁ with δ(C₁, C) = s₁ and δ(C₁, D) = s₁w, which has
  length k−1. For the second claim, go backwards from C_j: each step is a (WD2) move with a length increase, because
  every segment of a reduced word is reduced.
- (B3) *Residues.* "δ(C, D) ∈ W_J" is an equivalence relation, and its classes are the J-residues. If D′ ∈ R_J(D),
  then δ(C, D′) ∈ δ(C, D)·W_J.
  *Proof.* Join D to D′ by a gallery whose types lie in J, which is (B2) with a reduced word of δ(D, D′) ∈ W_J; such
  a word uses only letters of J. Each step changes δ(C, ·) to δ(C, ·)s or leaves it unchanged, by (WD2) and (B1).
- (B4) For every chamber C and every w ∈ W there is a chamber D with δ(C, D) = w. In particular every chamber has an
  *opposite* chamber, one with δ = w₀. *Proof.* Apply (WD3) repeatedly.
- (B5) With parameters, #{D : δ(C, D) = w} = q_w. Hence a J-residue has P_J = Σ_{u∈W_J} q_u chambers, and
  P_J = ∏_{s∈J}(1 + q_s) for a colour class J.
  *Proof.* Count galleries of a fixed reduced type from C. Step i has exactly q_{s_i} choices: in the s_i-panel of
  C_{i−1}, every chamber other than C_{i−1} is at distance δ(C, C_{i−1})s_i, by (WD2). A gallery of reduced type
  between two given chambers is unique, because a panel holds only one chamber at the shorter distance (also by WD2).

### 1.3 Theorem 1 (the diameter is h)

> **Theorem 1.** Let 𝒞 be a spherical building of irreducible type (W, S) of rank ≥ 2, with Coxeter number h and
> colour classes I₁, I₂, and let Γ be its bipartite flag graph. Then Γ is connected and every vertex has eccentricity
> exactly h; in particular diam Γ = h. More precisely:
> (a) d(R, R′) ≤ h for all vertices. Moreover d(R, R′) ≤ h − 1 when h is even and R, R′ have different types, and
> when h is odd and R, R′ have the same type.
> (b) If δ(C, C′) = w₀, then R_J(C) and R_K(C′) are at distance exactly h when (h even, K = J) or (h odd, K ≠ J), and
> at distance exactly h − 1 otherwise.

**Lemma 1 (edges are chambers).** An I₁-residue and an I₂-residue meet in at most one chamber. So C ↦
{R_{I₁}(C), R_{I₂}(C)} is a bijection from chambers to edges, and a vertex of type J has degree |R| = P_J.
*Proof.* If C, D both lie in both residues, then δ(C, D) ∈ W_{I₁} ∩ W_{I₂} = {1} by (C4), so C = D by (WD1).
Distinct chambers of R therefore lie in distinct residues of the other type. ∎

**Lemma 2 (a walk gives a product).** Let R₀, R₁, …, R_ℓ be a walk in Γ and J_i the type of R_i; these alternate.
Then δ(C, C′) ∈ W_{J₀} W_{J₁} ⋯ W_{J_ℓ} for every C ∈ R₀ and C′ ∈ R_ℓ.
*Proof.* Let E_i ∈ R_{i−1} ∩ R_i. In the sequence C, E₁, …, E_ℓ, C′, consecutive chambers share a residue: C, E₁ ∈ R₀;
E_i, E_{i+1} ∈ R_i; E_ℓ, C′ ∈ R_ℓ. Apply (B3) once per step. ∎

**Lemma 3 (a factorisation whose lengths add gives a walk).** Let R (type J₀) and R′ (type J_m) be vertices, C ∈ R,
C′ ∈ R′. Suppose δ(C, C′) = u₀u₁⋯u_m with u_i ∈ W_{J_i}, the J_i alternating, and ℓ(δ(C, C′)) = Σ ℓ(u_i). Then
d(R, R′) ≤ m.
*Proof.* Concatenate reduced words of the u_i. Because the lengths add, the result is a reduced word for δ(C, C′).
Take a gallery of this type from C to C′ (B2), and let F_i be its chamber at the end of the u₀⋯u_i part
(F₋₁ = C, F_m = C′). By (B2), δ(F_{i−1}, F_i) = u_i ∈ W_{J_i}, so V_i := R_{J_i}(F_{i−1}) = R_{J_i}(F_i). Since
residues of one type partition 𝒞, V₀ = R and V_m = R′. V_{i−1} and V_i have different types and share F_{i−1}, so
they are adjacent. Hence V₀, …, V_m is a walk of length m. ∎

*Proof of Theorem 1(a).* Let J = type(R), K = type(R′), C ∈ R, C′ ∈ R′, w = δ(C, C′).
1. By (C1), the word f_J made of h alternating blocks starting with c_J is a reduced word for w₀.
2. Since w ≤ w₀, (C2) gives a subword of f_J that is a reduced word for w. Group its letters by the block they come
   from: w = u₀⋯u_{h−1} with u_i ∈ W_{J_i}, J₀ = J, and the lengths add.
3. If J_{h−1} = K, Lemma 3 gives d ≤ h − 1. Otherwise append u_h = 1 ∈ W_K, and Lemma 3 gives d ≤ h.
4. Now J_{h−1} = J exactly when h is odd, which gives both bounds in (a). ∎

*Proof of Theorem 1(b).* Let R = R_J(C), R′ = R_K(C′) and take a shortest path of length ℓ.
1. By Lemma 2, w₀ ∈ W_{J₀}⋯W_{J_ℓ} with J₀ = J.
2. Every element of W_{J_i} has length ≤ |J_i|. So N ≤ Σ_{i=0}^{ℓ} |J_i|. With ℓ + 1 = 2p this sum is pr; with
   ℓ + 1 = 2p + 1 it is pr + |J|.
3. Both words in (C1) have N letters. When h is odd this forces |I₁| = |I₂| = r/2, with no classification needed.
4. *h even, K = J:* ℓ is even, and N = (h/2)r ≤ pr + |J| < (p+1)r, so p ≥ h/2 and ℓ = 2p ≥ h.
5. *h even, K ≠ J:* ℓ is odd, and pr ≥ hr/2, so ℓ = 2p − 1 ≥ h − 1.
6. *h odd, K ≠ J:* ℓ is odd, and pr ≥ hr/2, so p ≥ (h+1)/2 and ℓ ≥ h.
7. *h odd, K = J:* ℓ is even, and pr + r/2 ≥ hr/2, so ℓ ≥ h − 1.
8. With (a) these are equalities. By (B4) every chamber has an opposite chamber, so every vertex has eccentricity
   h. ∎

*Remarks.* (i) The proof never uses thickness, finite panels or a group action. It holds for thin buildings (the
Coxeter complex itself) and for buildings over infinite fields.
(ii) For rank 2 it is the classical fact that the incidence graph of a generalized m-gon has diameter m. For PG(2k, q)
the upper bound is CvB–K's Lemma 2.1 (odd–even transposition sort), and the exact value is Isham et al.'s
Theorem 6.11.
(iii) The reviewer's PG(4, q) pair at distance 5 is the case "h odd, different types" of (b): two flags that extend to
opposite chambers. Explicitly, with basis e₁, …, e₅, take (⟨e₁⟩ ⊂ ⟨e₁, e₂, e₃⟩) and (⟨e₄, e₅⟩ ⊂ ⟨e₂, e₃, e₄, e₅⟩). They
come from the opposite complete flags ⟨e₁⟩ ⊂ ⟨e₁, e₂⟩ ⊂ … and ⟨e₅⟩ ⊂ ⟨e₅, e₄⟩ ⊂ …, so they are exactly 5 apart.
(iv) `weyl_all.py` (→ `out/weyl_all.txt`) computes the distance function of Theorem 2 below over all of W for A₂–A₈,
B₂–B₇, D₄–D₇, G₂, F₄, E₆ and E₇ (2,903,040 elements). It finds eccentricity exactly h from both sides every time, on
the side that (b) predicts, with d(w₀) = h.
(v) `opposite_check.py` (→ `out/opposite_check.txt`) tests (b) directly in the real geometries. It samples random
pairs of chambers that are opposite by linear algebra: V_i + V′_{n+1−i} = V for PG(n, q), and V_i ∩ V′_i^⊥ = 0 for
polar spaces. It then measures the four distances between their odd and even parts. In 12 geometries (PG(n, q) with
n = 2–5, Sp, O, O⁻ and U polar spaces), every sampled distance is h or h − 1 exactly as (b) says.
(vi) All 21 flag graphs below pass the coordinator's all-pairs checker with diameter h (`out/apsp_checks.txt`,
`out/apsp_checks2.txt`). These include PG(4,3) (31,460 vertices) and Sp(8,2) (160,650).

### 1.4 Theorem 2 (distance formula) and the distance layers

> **Theorem 2.** For vertices R of type J and R′ of type K, and any C ∈ R, C′ ∈ R′ with w = δ(C, C′):
> d(R, R′) = min{ℓ ≥ 0 : ℓ ≡ [J ≠ K] (mod 2) and w ∈ W_{J₀}W_{J₁}⋯W_{J_ℓ}}, with J₀ = J and the J_i alternating.
> Equivalently, d = m_J(w) − [J_{m_J(w)} = K], where m_J(w) is the least m with w in the product of m alternating
> factors starting with W_J.

*Proof.* "≥" is Lemma 2. For "≤": every element of W_{J₀}⋯W_{J_ℓ} is the product of a subword of the concatenated
word (c_{J₀})(c_{J₁})⋯(c_{J_ℓ}). By (C3) it is also the product of a reduced subword. Grouping that subword by blocks
gives a factorisation whose lengths add, and Lemma 3 finishes. ∎

> **Corollary 2 (distance layers).** For a vertex R of type J, the number of K-vertices at distance d from R is
> (1/P_K)·Σ_{w ∈ W, d_{JK}(w) = d} q_w. It depends only on W, the parameters and J, not on R.

*Proof.* Fix C ∈ R. By Theorem 2, the distance from R to R_K(C′) depends only on δ(C, C′). Each K-vertex contains
P_K chambers, all giving that same distance. Count with (B5). ∎

*Check.* `weyl_dist.py` computes the prediction from W alone. `polar_flags.py` builds the actual graphs from linear
algebra over GF(2), GF(3), GF(4): projective, symplectic, parabolic, elliptic, hyperbolic (D₄) and Hermitian
geometries. `compare_dist.py` (→ `out/compare_dist.txt`) compares BFS layers from 4 vertices per side (one fixed,
three random) on 21 buildings:
- A₂ (q = 2, 3), A₃ (2, 3), A₄ (2, 3), A₅ (2);
- Sp(4, 2), Sp(4, 3), O(5, 3); Sp(6, 2), Sp(6, 3), O(7, 3); Sp(8, 2);
- O⁻(6, 2) = GQ(2,4), O⁻(6, 3) = GQ(3,9), O⁻(8, 2), U(4, 2) = GQ(4,2), U(5, 2) = GQ(4,8), U(6, 2);
- O⁺(8, 2) (type D₄).

Result: **ALL MATCH**, every layer and every vertex. For example, every vertex of the PG(4,3) graph sees
1, 16, 204, 2,268, 15,525, 13,446 vertices at distances 0–5.

### 1.5 Orders, degrees, and which buildings give regular graphs

With E = Σ_w q_w chambers, Γ has E/P_{I₁} vertices of type I₁ (each of degree P_{I₁}) and E/P_{I₂} of type I₂. It is
regular iff P_{I₁} = P_{I₂}. With equal parameters q, E = ∏[d_i]_q, where d_i are the degrees of W (Humphreys §3.15),
and Γ is regular iff |I₁| = |I₂|.

Finite thick buildings: rank ≥ 3 are those of the finite groups of Lie type (Tits); rank 2 are generalized polygons.
Parameters as in `table_cells.py`.

| type | buildings (parameters) | regular? |
|---|---|---|
| A_n | PG(n, q) | iff n even |
| C_n | Sp(2n, q), O(2n+1, q) (q,…,q) | iff n even |
| C_n | O⁻(2n+2, q) (q,…,q,q²), U(2n, q) (q²,…,q²,q), U(2n+1, q) (q²,…,q²,q³) | never |
| D_n | O⁺(2n, q) | never (classes differ by 1 or 2) |
| E₆, E₈ | E₆(q), E₈(q) | yes |
| E₇ | E₇(q) | no (3 + 4) |
| F₄ | F₄(q) | yes |
| F₄ | ²E₆(q) (q, q, q², q²) | **yes**: each class gets one q and one q² node, degree (q+1)(q²+1) |
| G₂ | G₂(q) = GH(q, q) | yes (Moore) |
| G₂ | ³D₄(q) = GH(q, q³) | no |
| I₂(8) | ²F₄(q) = GO(q, q²) | no |
| C₂ | GQ(s, t), s ≠ t (incl. AS(q) = GQ(q−1, q+1)) | no |

For the twisted C_n, the class containing the special node n has product (1+s)^{⌈n/2⌉−1}(1+t), and the other has
(1+s)^{⌊n/2⌋}. These can only be equal when n is even and s = t. REGULARITIES listed "B_{2m}/C_{2m}" as regular
without the equal-parameter condition, and missed ²E₆.

### 1.6 Theorem 3 (Delorme's product reaches every h)

> **Theorem 3.** Let G be a connected bipartite graph with parts A, B and diameter D ≥ 1. Let G ⊗ Opp(G) be the graph
> on (A×B) ⊔ (B×A) with (x, y) ~ (x′, y′) iff xx′ and yy′ are edges of G. Then:
> - it is bipartite with parts A×B and B×A;
> - deg(x, y) = deg x · deg y;
> - d((x, y), (x′, y′)) = max(d(x, x′), d(y, y′)), so its diameter is exactly D.
>
> Its quotient Q by (x, y) ↦ (y, x) has vertex set A×B, with (x, y) ~ (x′, y′) iff x ~ y′ and y ~ x′ (loops dropped).
> Q has |A||B| vertices and diameter ≤ D − 1.

*Proof.* A walk of length m in the product is a pair of walks of length m in G. In a connected bipartite graph with
an edge, x and x′ are joined by a walk of length m iff m ≥ d(x, x′) and m ≡ d(x, x′) (mod 2): pad with back-and-forth
steps. Inside each part of the product, d(x, x′) and d(y, y′) have the same parity, which gives the distance formula.
A walk in Q of length m from (x, y) to (x′, y′) is a walk in the product from (x, y) to (x′, y′) if m is even, or to
(y′, x′) if m is odd. So d_Q = min(max(d(x,x′), d(y,y′)), max(d(x,y′), d(y,x′))). One of the two maxima involves only
distances of the parity that is ≤ D − 1. ∎

The construction is Delorme's (J. Graph Theory 9 (1985) 325–334, "Large bipartite graphs with given degree and
diameter"). It was used there and later with generalized quadrangles (Isham et al. §3.4.2 and Table 3; Comellas,
arXiv:2406.18994).

**Corollary 3.** For a building flag graph Γ, Γ ⊗ Opp(Γ) is regular of degree ∏_{s∈S}(1 + q_s), with order
2E²/∏_{s∈S}(1 + q_s) and diameter h, for every type, balanced or not. Q(Γ) is a general graph of diameter ≤ h − 1
with order E²/∏(1 + q_s).

*Check.* `delorme.py` + `run_checks.sh` (→ `out/apsp_checks.txt`, coordinator's apsp.c, all pairs) on six products:
PG(2,3), Sp(4,2), GQ(2,4), PG(3,2), GQ(3,9), GQ(4,8). They have 338 to 98,010 vertices, degrees 9 to 45. Each is
regular with diameter = h; each quotient has diameter h − 1. apsp prints "RESULT INVALID" for the quotients only
because they are not bipartite.

### 1.7 Theorem 4 (how fast the ratio tends to 1)

> **Theorem 4.** As q → ∞ through prime powers:
> (a) Balanced building with equal parameters, rank r = 2t ≥ 4, Coxeter number h, degree Δ = (q+1)^t:
> n/M_b(Δ, h) = 1 − t(h−2)/q + O(q⁻²). For t = 1 (generalized polygons with s = t = q) n = M_b exactly.
> (b) Delorme product of a building of rank r, equal parameters, Δ = (q+1)^r: n/M_b(Δ, h) = 1 − r(h−2)/q + O(q⁻²).
> (c) ²E₆(q), Δ = (q+1)(q²+1): n/M_b(Δ, 12) = 1 − 10/q + O(q⁻²).
> (d) For every D ≥ 2: lim_{Δ→∞} n_b(Δ, D)/M_b(Δ, D) = 1. This is the full limit over all Δ, not only along prime
> powers. (D = 2 is K_{Δ,Δ}; the proof below is for D ≥ 3.)

*Proof of (a).*
1. Each [d]_q = q^{d−1}(1 + q⁻¹ + O(q⁻²)), and every d_i ≥ 2, so E = q^N(1 + r/q + O(q⁻²)).
2. Hence n = 2E/(q+1)^t = 2q^{t(h−1)}(1 + t/q + O(q⁻²)), using N − t = t(h−1).
3. Δ − 1 = q^t(1 + t/q + O(q⁻²)) because t ≥ 2. So
   M_b = 2(Δ−1)^{h−1}(1 + O(Δ⁻¹)) = 2q^{t(h−1)}(1 + t(h−1)/q + O(q⁻²)).
4. Divide. ∎

(b) is the same computation with E² and r in place of E and t. (c) uses E = q³⁶(1 + 2/q + …): the coefficient of q³⁵
counts the two simple reflections with parameter q.

*Proof of (d).* n_b is non-decreasing in Δ. Given Δ, let q be the largest prime with (q+1)^{D−1} ≤ Δ. By the prime
number theorem, (q+1)^{D−1} = (1 − o(1))Δ. Use the Delorme product of the A_{D−1}(q) flag graph (diameter D by
Theorems 1 and 3), and (b). M_b(x, D) ~ 2x^{D−1} absorbs the (1 − o(1)) factor. ∎

The same limit follows from CvB–K's Theorem 1.1 together with n_b(Δ, D) ≥ 2n(Δ−1, D−1) (the graph B(H), x₀ ~ y₁ iff
x = y or xy ∈ E(H)). See §1.9.

*Checks.* `asymptotic_check.py` (→ `out/asymptotic_check.txt`) prints q(1 − n/M_b) at q = 1009, 10007, 100003:
- A₄: 5.9997 (predicted 6), A₆: 14.9988 (15), C₄: 11.9991 (12);
- F₄: 19.9978 (20), E₆: 29.9953 (30), ²E₆: 9.9995 (10), E₈: 111.94 (112);
- A₃ ⊗ Opp: 5.9998 (6), B₅ ⊗ Opp: 39.9917 (40); G₂: 0 (Moore).

`rates.py` (→ `out/rates.txt`) gives exact ratios for D = 3…30 and the first q at which each route reaches 50 % and
90 % of the Moore bound. Selected rows, best building route per D (Δ where it first reaches 50 % / 90 %):

| D | best building route | 1 − n/M_b ≈ | 50 % at Δ | 90 % at Δ | doubled CvB–K at q = 16 |
|---|---|---|---|---|---|
| 3, 4, 6 | PG(2,q), GQ(q), GH(q) | 0 (Moore) | 3 | 3 | 0.79, 0.49, 0.09 |
| 5 | A₄(q) | 6Δ^(−1/2) | 81 | 3,600 | 0.24 (Δ ≈ 6.5·10⁹) |
| 7 | A₆(q) | 15Δ^(−1/3) | 13,824 | 3.4·10⁶ | 0.029 (Δ ≈ 5.4·10¹⁴) |
| 8 | Sp(8, q) | 12Δ^(−1/2) | 324 | 12,996 | 0.007 |
| 9 | A₈(q) | 28Δ^(−1/4) | 3.1·10⁶ | 5.3·10⁹ | 0.0013 |
| 10 | B₅(q) ⊗ Opp | 40Δ^(−1/5) | 7.8·10⁸ | 7.9·10¹² | ≈ 0 |
| 12 | F₄(q) | 20Δ^(−1/2) | 900 | 36,864 | ≈ 0 |
| 16 | Sp(16, q) | 56Δ^(−1/4) | 4.5·10⁷ | 8.6·10¹⁰ | – |
| 18 | E₇(q) ⊗ Opp | 112Δ^(−1/7) | 3.2·10¹⁵ | 1.5·10²¹ | – |
| 30 | E₈(q) | 112Δ^(−1/4) | 7.2·10⁸ | 1.3·10¹² | – |

At D = 12, ²E₆(q) is the best of the three regular exceptional families at a given small q: 0.53 at q = 16, against
0.31 for F₄. F₄ still wins at equal Δ, because its degree is (q+1)² rather than about q³. For D ≡ 2 mod 4 with
D ≥ 10 and D ≠ 30 there is no regular flag graph (§1.5), so the Delorme product of B_{D/2}, or of E₇ at D = 18, is the
best building route. It squares the degree.

**(f) Side remark: general graphs.** Delorme's quotient Q(Γ) of the A_D(q) flag graph has diameter ≤ D, degree
≤ (q+1)^D, and |Q|/Δ^D = 1 − D(D−1)/q + O(q⁻²). With the prime number theorem this re-proves CvB–K's Theorem 1.1
(lim n(Δ, D)/Δ^D = 1 for all D), with deficiency D(D−1)Δ^(−1/D) instead of their D(2D−1)Δ^(−1/(2D)). For odd D the
quotient of B_{(D+1)/2}(q) does better, (D+1)(D−1)/2·Δ^(−2/(D+1)). For even D, Isham et al.'s polarity quotient of
C(D/2, q) is better still. `general_rates.py` → `out/general_rates.txt`. The constants D(D−1), r(D−1) and CvB–K's
D(2D−1) are confirmed numerically by `general_asymptotic_check.py` → `out/general_asymptotic_check.txt`. For example,
at D = 5 the B₃ quotient reaches
0.49 at Δ = 4,913, while H_{5,q} is at 0.09 at Δ ≈ 1.9·10¹². CvB–K's Remark 3.2 asks for the optimal rate. The exact
degree of H_{k,q} used here is Σ_{T} q^{|T|}(q+1)^{|N(T)|}, over non-empty sets T of odd nodes of A_{2k}, where N(T) is
the set of even nodes adjacent to T. It is the d = 2 layer of Corollary 2 and matches BFS (60 and 204 for k = 2,
q = 2, 3).

### 1.8 Table cells: which ones the family touches, and how close it gets

`table_cells.py` (→ `out/table_cells.txt`) lists every graph the theory produces with max degree ≤ 16 and diameter
3–10. That covers flag graphs of all finite thick buildings with their real parameters, Delorme products, and
Kronecker products of two regular flag graphs with the same h. Each is compared with the 2013 table, our best value
and the Moore bound.

**Cells hit directly, apart from Moore graphs** (order; share of table; share of ours; share of Moore):

| D | cell | graph | order | /table | /ours | /Moore |
|---|---|---|---|---|---|---|
| 3 | (16,3) | PG(2,3) ⊗ Opp | 338 | 0.86 | 0.85 | 0.70 |
| 4 | (7,4) | GQ(4,6) = AS(5) | 300 | 0.87 | 0.84 | 0.58 |
| 4 | (11,4) | GQ(8,10) = AS(9) | 1,620 | 0.93 | 0.91 | 0.73 |
| 4 | (13,4) | GQ(10,12) = AS(11) | 2,904 | 0.95 | 0.92 | 0.77 |
| 4 | (15,4) | GQ(12,14) = AS(13) | 4,732 | 0.96 | 0.93 | 0.80 |
| 4 | (15,4) | GQ(2,4) ⊗ Opp | 2,430 | 0.49 | 0.48 | 0.41 |
| 4 | (16,4) | A₃(3); GQ(3) ⊗ Opp | 650; 3,200 | 0.13; 0.62 | 0.12; 0.59 | 0.09; 0.44 |
| 5 | (9,5) | A₄(2) | 2,170 | 0.87 | 0.82 | 0.23 |
| 5 | **(16,5)** | **A₄(3)** | **31,460** | **1.15** | 0.93 | 0.29 |
| 6 | (9,6) | ³D₄(2) = GH(2,8); C₃(2); GH(2) ⊗ Opp | 3,276; 1,260; 7,938 | ≤ 0.11 | | ≤ 0.11 |
| 6 | (15,6) | U(6,2); O⁻(8,2); GH(2) ⊗ GH(4) | 24,948; 6,426; 171,990 | ≤ 0.21 | | ≤ 0.15 |
| 6 | (16,6) | C₃(3); GH(3) ⊗ Opp | 18,200; 264,992 | ≤ 0.30 | | ≤ 0.16 |
| 8 | (5,8) | GO(2,4) (Ree–Tits octagon) | 4,680 | 0.51 | 0.49 | 0.11 |
| 8 | (9,8) | C₄(2) = Sp(8,2) | 160,650 | 0.36 | 0.30 | 0.034 |
| 8 | (15,8) | GO(2,4) ⊗ Opp; O⁻(10,2) | 10,266,750; 1,413,720 | 0.72; 0.10 | 0.57 | 0.045 |
| 8 | (16,8) | C₄(3) = Sp(8,3) | 23,878,400 | 0.66 | (no value of ours) | 0.065 |

Columns D = 7, 9, 10 are not hit at all: every building with h ∈ {7, 9, 10} has Δ ≥ 27 at q = 2. The best-per-cell
grid, where graphs of smaller degree or diameter also count, is in `out/table_cells.txt` (section B); it never
reaches our value outside the Moore cells.

So:
- **(16,5) is the only cell above the 2013 table.** It is CvB–K's graph (already published), and our route-chart
  lift with 33,792 vertices beats it.
- The near misses at D = 4 are the AS(q) quadrangles. Our Theorem A (2q²(q+2), research/NOTE.md) is exactly AS(q)
  plus two elliptic quadrics, made regular; it beats them by 2q² vertices.
- In the table range, every flag graph of a building of rank ≥ 3 is ≤ 0.29 of the Moore bound. The rank-2 AS(q)
  quadrangles reach 0.80 at (15,4). The asymptotics only take over at Δ in the hundreds or thousands (table in §1.7).

### 1.9 Literature: what is known and what is not

Searched by an 8-card Haiku squad (research/squads/buildings-r1-lit/c1–c8/notes.md). I checked the key items myself
(marked ✓).

- ✓ **Miller–Širáň, DS14v2 (2013), p. 36:** "β_D = lim inf b_{Δ,D}/(2Δ^{D−1}) … so far, it is only known [Delorme
  1985a,b] that equality holds for D = 2, 3, 4 and 6." p. 19: for general graphs μ_D = 1 only for D = 1, 2, 3, 5, and
  μ₄ ≥ 1/4.
- **Delorme, J. Graph Theory 9 (1985):** the abstract (Crossref/OpenAlex, via cards c1 and c6) proves only
  lim inf n_b Δ^{1−D} > 0 for every D. It introduces G ⊗ Opp(G) (Isham et al. §3.4.2). The full text is behind
  Wiley; not read.
- ✓ **Cames van Batenburg–Korsky, arXiv:2608.03965 (Aug 2026):**
  - lim n(Δ, D)/Δ^D = 1 for every D, via halved flag graphs of A_{2k};
  - Lemma 2.1 is the type-A upper bound of Theorem 1;
  - their Lean repository (github.com/woutercvb/wewantmoore) covers the general theorem.

  The only "bipartite" limit in the paper (p. 2) and in the Lean README ("the bipartite-restricted exact limit … odd-
  cycle-free upper bound") is the edge/line-graph version. Card c4 read it as the vertex version; it is not.
- ✓ **Isham–Lakhotia–Monroe–Petrini, arXiv:2608.27253 (v2, 22 Oct 2026):**
  - Thm 6.11: diam C(k, q) = 2k + 1 exactly (type A case of Theorem 1);
  - polarity quotients of C(k, q) (general, even D);
  - Kronecker products;
  - Delorme's Opp construction for quadrangles only.

  No other building types appear in either paper.
- ✓ (C1) is Fomin–Zelevinsky 2003, Lemma 2.1 (Bourbaki V §6 Ex. 2).
- Bachratý, PhD summary 2021 (card c7): "not a single known construction (relevant to this problem) based on
  generalised octagons".
- Bachratý–Šiagiová–Širáň, arXiv:1709.09760 (2017), introduction (card c2): lim sup n(Δ, k)/Δ^k = 1 was known only
  for k ∈ {2, 3, 5}; for k = 7 the best was ≥ 1.57⁻⁷.

  Yet Delorme's 1985 construction already gave k = 7. Apply Theorem 3 to the Ree–Tits octagons GO(q, q²),
  q = 2^(2e+1):
  - the quotient is a general graph of diameter ≤ 7;
  - the product is a bipartite graph of diameter 8;
  - both have order ~ q²¹ and degree (q+1)(q²+1).

  So lim sup n(Δ, 7)/Δ⁷ = 1 and lim sup n_b(Δ, 8)/M_b(Δ, 8) = 1. `asymptotic_check.py` gives ratios 0.455 at q = 8,
  0.827 at q = 32, 0.954 at q = 128 and 0.997 at q = 2048. This seems to have gone unnoticed for 40 years. CvB–K
  (general) and Sp(8, q) (bipartite, every q, faster) now cover both.
- Not found anywhere: Theorem 1 beyond type A and rank 2; Delorme's product applied to higher-rank flag graphs; the
  bipartite limit for any D ∉ {2, 3, 4, 6}; any rate for the bipartite problem.

**Verdict.** The statement "lim n_b(Δ, D)/M_b(Δ, D) = 1" is not in print for any D ∉ {2, 3, 4, 6}. It is a one-line
corollary of CvB–K (August 2026) via the standard doubling, so it should be credited to them. What is ours:
- Theorem 1 for all types (the type-A case is theirs);
- the observation that Delorme's 1985 product plus Theorem 1 gives every D directly, and, for general graphs,
  re-proves their theorem;
- the convergence rates, which are much faster than the 2026 constructions give;
- the historical footnote that Delorme's product on the Ree–Tits octagons already gave general D = 7 and
  bipartite D = 8 (lim sup).

---

## 2. Conjectured, with strong evidence

### 2.1 Only the colour classes give a family that loses no power of q

Split S = J₁ ⊔ J₂ in any way, not only into the colour classes. Residues of the two types still meet in at most one
chamber (C4), so the graph is defined, with degrees ~ q^{a₂}, q^{a₁} (a_i = ℓ(w_{J_i})), order ~ q^{N − min a} and
diameter D given by the same block distance. The Moore bound with this degree is ~ q^{max(a)(D−1)}. Call the lost
power gap = max(a)(D−1) − (N − min a) ≥ 0.

`partitions.py` (→ `out/partitions.txt`) checks all 2-partitions of A₂–A₆, B₂–B₅, D₄, D₅, F₄ and G₂ by brute-force
BFS over all of W.

`partitions2.py` (→ `out/partitions2.txt`) does the same for every crystallographic type of rank ≤ 8: A₂–A₈, B₂–B₈,
D₄–D₈, E₆, E₇, E₈, F₄, G₂, up to 127 splittings each. It does not enumerate W. An alternating product of parabolic
subgroups is a Bruhat interval [e, δ], with δ the Demazure product of the longest elements. So a J-vertex has
eccentricity "the number of blocks after which δ = w₀". On the 13 types they share, the two methods agree.

Result: gap = 0 only for the colour classes of the balanced types (A₂, A₄, A₆, A₈, B₂, B₄, B₆, B₈, E₆, E₈, F₄, G₂).
The best non-colour split is A₄ with {s₁, s₄} | {s₂, s₃} (diameter 4, gap 1). Every other non-colour split loses at
least 3 powers of q, and E₈ at least 29.

**What is proved (reduction).** gap = 0 iff a₁ = a₂ = a and w₀ = w_{J₁}w_{J₂}w_{J₁}⋯ = w_{J₂}w_{J₁}w_{J₂}⋯ (N/a
factors each, lengths adding).

*Proof.*
1. (⇒) Let J₂ have the smaller a and m = m_{J₂}(w₀) ≤ D. The Demazure product of m blocks has length at most
   ⌈m/2⌉a₂ + ⌊m/2⌋a₁, so N is at most that.
2. Hence gap ≥ a₁(m−1) + a₂ − N ≥ (⌈m/2⌉ − 1)(a₁ − a₂) ≥ 0.
3. m ≤ 2 is impossible for a connected diagram. N > a₁ + a₂, because a root such as α_i + α_j with i ∈ J₁ and
   j ∈ J₂ adjacent belongs to neither parabolic.
4. So gap = 0 forces a₁ = a₂ = a, D = m and N = ma. Then every Demazure step adds length, so each block is the
   longest element and the lengths add. The same holds from J₁, since N/a ≤ m_{J₁}(w₀) ≤ D = N/a.
5. (⇐) The factorisations give D ≤ N/a, so gap ≤ 0. ∎

A necessary condition follows: if some s ∈ J₁ commutes with all of J₂, then s is a left descent of w_{J₂}w_{J₁}, and
w_{J₁}w_{J₂}w_{J₁} is not reduced. So the conjecture says that the colour classes are the only "longest-element
analogue" of a bipartite Coxeter element. A proof needs that analogue of (C1). I expect it to hold for all types;
the computation above covers rank ≤ 8.

### 2.2 For D ≡ 2 mod 4 the building rate is genuinely worse

For D ≡ 2 mod 4, D ≥ 10, D ≠ 30, no finite thick building gives a regular flag graph (§1.5; this part is proved from
the classification). The best building rate we have is Δ^(−2/D), against Δ^(−4/D) for D ≡ 0 mod 4 and Δ^(−2/(D−1))
for odd D. Whether some other structured family does better at these D is open; nothing in the literature addresses
it.

## 3. Weak patterns

- **Convergence is slow and gets slower with D.** The first-order constant t(h−2) grows like D², and the exponent
  shrinks like 1/D. Inside the table (Δ ≤ 16) the asymptotics never matter except for the Moore graphs (D = 3, 4, 6).
- **Unequal parameters can help at finite q.** ²E₆(q) beats E₆(q) and Sp(12, q) at every q; it reaches 50 % of Moore at
  q = 16. At D = 4 the AS(q) quadrangles GQ(q−1, q+1) come within 4–7 % of the table, closer than any other non-Moore
  building graph.
- **The two sides need not look alike.** Sp(8, 2) is 9-regular, but its sides see different layers: 1,608 versus
  1,512 vertices at distance 4. Corollary 2 explains this; there is no polarity swapping the sides of C₄.

## 4. Dead ends (tested and dropped)

| idea | test | result |
|---|---|---|
| other splittings of the diagram | partitions.py, partitions2.py: all 2-partitions, all types of rank ≤ 8 | lose ≥ 1 power of q (§2.1) |
| unbalanced flag graphs as they are (A_odd, C_odd, D_n, E₇, twisted C_n, ³D₄, ²F₄, GQ(s,t)) | §1.5, table_cells.py | max degree is the larger side; lose a power of q; in range 0.8 %–96 % of the table, never above |
| Kronecker products of two same-h regular flag graphs in range | table_cells.py (K rows) | ≤ 0.80 of the table (D = 3), ≤ 0.62 (D = 4), ≤ 0.30 (D = 6) |
| Delorme products in range | table_cells.py (P rows) | best (15,8) 10,266,750 = 0.72 of the table, 0.57 of ours |
| general table via Delorme or polarity quotients | general_rates.py and the wiki general table ("as of 14 October 2026") | below everywhere: (16,4) A₄(3) quotient 15,730 vs 16,384; (9,4) 1,085 vs 1,765; (15,3) GQ(2,4) quotient 1,215 vs 1,539; (15,7) GO(2,4) quotient 5,133,375 vs 9,758,988 |
| polygon covers with building bases (REGULARITIES §1.3) | arithmetic | C₄(2) + 1 matching over Z₃ at (10,9): 481,950 vs 7,057,400 |
| (previous session) lifts of A₄(3), affine A₄(3), C₄ at (9,8)/(16,8) | REGULARITIES §1.2, §4 | unique walks; diameter 8; below the table |

## 5. What was wrong or missing in REGULARITIES §1.2, and the fix

The reviewer's own text is not in the repo; these are the gaps I found.

1. **"d(x, y) ≤ ℓ iff w is a product of ℓ − 1 alternating elements."**
   - Only the "only if" half is immediate.
   - A factorisation of δ(C, C′) gives intermediate chambers ending at C′ only when the lengths add (Lemma 3, from
     galleries of reduced type).
   - For an arbitrary factorisation, the deletion condition supplies one whose lengths add (Theorem 2).
   - The subword argument used for the upper bound does produce lengths that add, so the bound was right; the proof
     needed this step.
2. **No lower bound.** "Diameter = h" was only computed on seven cases. Theorem 1(b) proves it for every type, via
   opposite chambers and a letter count. It covers the reviewer's PG(4, q) pair.
3. **Regularity.** "B_{2m}/C_{2m}" is regular only with equal parameters (Sp(4m, q), O(4m+1, q)). O⁻ and the unitary
   forms are not. ²E₆(q) is regular and was missing.
4. **Asymptotics.**
   - "lim along prime powers" is a lim sup. The full limit needs monotonicity and the prime number theorem.
   - "D ≡ 2 mod 4 is not reached" is false (Theorem 3).
   - The whole statement is a corollary of CvB–K (§1.9).

## 6. Open questions for a next session

1. Prove §2.1 (only the colour classes are tight). The tight case needs w₀ to factor, with lengths adding, into about
   N/a alternating longest elements of two complementary parabolic subgroups.
2. Delorme's J. Graph Theory 1985 paper is behind Wiley. Does it treat the octagons? §1.9 says the octagon case
   seems unnoticed; the full text would settle it.
3. Lower bounds on the rate: is 1 − n_b(Δ, 5)/M_b(Δ, 5) ≥ cΔ^(−1/2) for some c > 0? Nothing is known.
4. Lean: Theorem 1 needs only the W-metric axioms and three Coxeter facts. The Coxeter facts are the hard part to
   formalise in general. For one fixed W, e.g. W(B₄) with 384 elements, the facts actually used become finite
   statements that a computation could certify. (C2) and (C3) are needed only for the factorisations that occur.

## Scripts and outputs (research/theorems/buildings/)

| script | output | what |
|---|---|---|
| coxeter_check.py | out/coxeter_check.txt | (C1) and N = rh/2 for 40 types; letter counts for the lower bound |
| weyl_dist.py | (library; run directly for one type) | Theorem 2 / Corollary 2: predicted distance layers from W |
| weyl_all.py | out/weyl_all.txt | eccentricity h over all of W, 19 Weyl groups up to E₇ |
| polar_flags.py | (graphs) | flag graphs of PG, Sp, O, O⁻, O⁺, U geometries over GF(2), GF(3), GF(4), from the definitions |
| compare_dist.py | out/compare_dist.txt | BFS layers vs Corollary 2 on 21 buildings: all match |
| delorme.py, run_checks.sh | out/apsp_checks.txt | coordinator's apsp.c on 9 flag graphs, 6 Delorme products, 6 quotients |
| table_cells.py | out/table_cells.txt | §1.8, every building-derived graph in the table range |
| rates.py | out/rates.txt | §1.7, ratios to Moore for D = 3…30, three routes |
| asymptotic_check.py | out/asymptotic_check.txt | first-order constants of Theorem 4 |
| general_rates.py | out/general_rates.txt | §1.7(f), general graphs |
| general_asymptotic_check.py | out/general_asymptotic_check.txt | first-order constants for general graphs |
| run_checks2.sh | out/apsp_checks2.txt | apsp.c on the other 12 flag graphs of compare_dist.py |
| opposite_check.py | out/opposite_check.txt | Theorem 1(b) tested directly on random opposite chamber pairs |
| partitions.py | out/partitions.txt | §2.1, brute force over W |
| partitions2.py | out/partitions2.txt | §2.1 up to rank 8 incl. E₈, via Demazure products |
