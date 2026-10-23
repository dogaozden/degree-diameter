# Random Haar graphs: threshold theorems for diameter ≤ D

theory job "cd-theory", 2026-10-23 (cloud session). Companion files: `LITERATURE.md` (what is known),
`DATA_CHECK.md` (tests against our records and Monte Carlo), `SUMMARY.md` (one page), scripts in `scripts/`.

**Status tags.** **[PROVED]** = complete proof here, using only the cited standard tools.
**[PROVED, cited input]** = complete proof, except for one cited external fact, named in place.
**[SKETCH, gap Gk]** = argument with exactly one missing step, named Gk. **[CONJECTURE]** = not proved.

**Short version.**
- Theorem 1 and Theorem 2 hold for every S. Theorem 1 is the Moore-type bound n ≤ W(Δ,D). Theorem 2 is an
  abelianization bound, |G/G'| ≤ A(Δ,D) = O(D^{Δ−1}), so abelian Haar graphs have polynomial order.
- Theorems 3 and 4 hold for **every finite group G**, with D fixed and Δ → ∞. They show that a random S has
  diameter ≤ D essentially iff μ̃ := Σ_x exp(−C(Δ,D−1)·β(x)) → 0. Here β(x) is the probability that some ordering
  of D−1 independent uniform elements, with alternating signs, multiplies to x.
- Consequence (Corollary 4.2): for every group the threshold lies between n ln n and (D−1)!·n ln n words.
  - Lower end, n ln n: attained when there are few coincidences. It is conditional for SL(2,q) (gap G1).
  - Upper end: for abelian groups the threshold is at least ⌈ℓ/2⌉!⌊ℓ/2⌋!·n ln n (ℓ = D−1).
  - PSL(2,q) and PGL(2,q) at odd D: the threshold is at least (4/3)·n ln n (proved).
- The records' regime (Δ fixed, D → ∞) is a conjecture, with the missing step named exactly (gap G2, §4).

---

## 0. Notation and the covering lemma

G is a finite group of order n. S = (s_1, …, s_Δ). H(G,S) has vertices G × {A,B} and edges (g,A) ~ (sg,B), s ∈ S.
Write ℓ := D − 1.

**Words.** A walk from (e,A) uses letters s_{i_1}, s_{i_2}, … with signs +, −, +, … and ends at the group element
s_{i_L}^{ε_L} ⋯ s_{i_2}^{−1} s_{i_1}, where ε_j = (−1)^{j−1}. Call this an *A-word* of length L. A walk from (e,B)
gives a *B-word*, with signs ε_j = (−1)^j.

A word is *reduced* if consecutive indices differ (i_{j+1} ≠ i_j). Equivalently, the walk does not backtrack. Distinct
reduced words are distinct elements of the free group F_Δ, because alternating signs prevent any cancellation.
There are Δ(Δ−1)^{L−1} reduced words of length L ≥ 1.

**Lemma 0.1 (covering) [PROVED].**
- D even: diam H(G,S) ≤ D iff every x ∈ G is the value of an A-word of length exactly ℓ. Equivalently, every x is
  the value of a reduced A-word of odd length ≤ ℓ.
- D odd: diam H(G,S) ≤ D iff every x is the value of an A-word of length ℓ **and** of a B-word of length ℓ.

*Proof.* Right multiplication (g,X) ↦ (gh,X) is an automorphism, so it suffices to look at distances from (e,A)
and (e,B).
- A vertex at distance j ≤ L with j ≡ L (mod 2) is the endpoint of a walk of length exactly L: pad the shortest
  path with back-and-forth steps.
- A non-reduced word equals a shorter word of the same parity, by cancelling a factor s s^{−1}.
- D even, "if": A–B distances are ≤ ℓ. A–A distances are ≤ 1 + ℓ = D, via a neighbour (sg,B). B–B is similar.
- D even, "only if": d((e,A),(x,B)) is odd and ≤ D, so it is ≤ ℓ.
- D odd: same-side distances are even and ≤ D, so they are ≤ ℓ. A–B distances are then ≤ 1 + ℓ. ∎

The sufficiency direction is formalised in `lean/BipartiteDD/Haar/GraphD.lean` (`haar_ediam_le_even`,
`haar_ediam_le_odd`). The necessity direction is elementary and is not used there.

**W(Δ,D)** is the number of reduced words of the binding parity and length ≤ ℓ (heuristic.py, sizelaw/data.py):

  W(Δ,D) = Σ_{L ≤ ℓ, L ≡ ℓ (2)} Δ(Δ−1)^{L−1}, with the empty word counted once for odd D.

---

## 1. Bounds for every S (counting)

**Theorem 1 (Moore-type bound) [PROVED].** For every group G and every S with |S| = Δ, diam H(G,S) ≤ D implies

  n ≤ W(Δ,D) = Σ_{j=0}^{D−1} (Δ−1)^j.

*Proof.* By Lemma 0.1, G is covered by the values of reduced words of the binding parity, and there are W of them.
The identity follows by pairing the terms:
- D = 2k: Σ_{i<k} Δ(Δ−1)^{2i} = Σ_{i<k} [(Δ−1)^{2i} + (Δ−1)^{2i+1}].
- D = 2k+1: 1 + Σ_{i=1}^{k} Δ(Δ−1)^{2i−1} = 1 + Σ_{i=1}^{k} [(Δ−1)^{2i−1} + (Δ−1)^{2i}].

`scripts/data_check.py` checks the identity numerically for Δ = 3..19 and D = 2..11. ∎

*Remarks.*
1. Theorem 1 is **exactly** the bipartite Moore bound per side. SIZE_LAW §5(b) says "slightly below the bipartite
   Moore bound"; in fact the two are equal. Consequently C_D := n/(Δ−1)^{D−2} ≤ Δ g_Δ (1 + O(Δ^{−2})) for every S.
2. **No log-factor improvement is possible for arbitrary S.** At D = 3, a Singer difference set S ⊂ Z_{q²+q+1}
   gives the incidence graph of PG(2,q). That graph has n = q² + q + 1 = W(q+1, 3). So the ln n factor below is a
   property of *random* S, not of Haar graphs. The question for structured S at D ≥ 7, where bipartite Moore graphs do
   not exist (Feit–Higman), is open; see SIZE_LAW §4.3.

**Theorem 2 (abelianization bound) [PROVED].** Let G' = [G,G] and let A(Δ,D) be the number of c ∈ Z^Δ with
Σ c_i = ε (ε = 1 for D even, 0 for D odd), ‖c‖₁ ≤ ℓ and ‖c‖₁ ≡ ℓ (mod 2). Then diam H(G,S) ≤ D implies

  |G/G'| ≤ A(Δ,D), and hence n ≤ |G'|·A(Δ,D).

For fixed Δ, A(Δ,D) = Θ(D^{Δ−1}) (a polynomial). For Δ → ∞ with D fixed,
A(Δ,D) ~ Δ^ℓ/(⌈ℓ/2⌉!⌊ℓ/2⌋!) ~ W/(⌈ℓ/2⌉!⌊ℓ/2⌋!).

*Proof.* The image of a word's value in G/G' is Σ_i c_i s̄_i, where c is the signed letter count. The count c
satisfies the three constraints because the signs alternate and the length has the parity of ℓ. Each covered x̄
needs one such c. ∎

*Remarks.*
- Words with the same signed letter count agree in G/G'. In particular, any two **sign-preserving rearrangements**
  of a word agree there. This is the mechanism behind the abelian constant in Corollary 5.3 and the
  "rearrangement" coincidences of §3.
- Numbers: A(8,8) = 15,128, against W(8,8) = 960,800. Every record satisfies the bound, the largest ratio being
  |G^ab|/A = 0.33 (`scripts/data_check2.py`).

---

## 2. Random S, D fixed: the per-target law (every finite group)

**Model.** s_1, …, s_Δ are i.i.d. uniform on G. For D ≥ 4 in the regime below, Δ²/n → 0, so the s_i are distinct
whp. Every statement then transfers to a uniform Δ-subset, since conditioning on an event of probability 1 − o(1)
changes probabilities by o(1). For D = 3 the statements are for the i.i.d. model.

**Notation.**
- ℓ = D − 1 ≥ 2. N_ℓ := C(Δ,ℓ). W* := N_ℓ·ℓ! = Δ(Δ−1)⋯(Δ−ℓ+1).
- λ := W/n and λ* := W*/n.
- *Sides*: σ ∈ {B} for D even (A-words), σ ∈ {A, B} for D odd.
- For a set T ⊆ [Δ] with |T| = ℓ and a bijection π : [ℓ] → T, w^σ_π is the side-σ word of length ℓ with letters
  s_{π(1)}, …, s_{π(ℓ)}. These are the *distinct-letter words on T*; there are ℓ! of them.

**Definition (β).** Let t_1, …, t_ℓ be i.i.d. uniform in G. Then

  β_σ(x) := P( ∃ π ∈ Sym(ℓ) : t_{π(ℓ)}^{ε_ℓ} ⋯ t_{π(1)}^{ε_1} = x ).

Equivalently, β_σ(x) = P(B^σ_{T,x}), where B^σ_{T,x} := {some distinct-letter word on T takes the value x}.

- β is a class function: conjugating every t_i conjugates the product.
- 1/n ≤ β_σ(x) ≤ ℓ!/n. The lower bound holds because one fixed arrangement is uniform.
- β_σ(x) = ℓ!/n exactly iff the ℓ! arrangements never coincide at x.
- Bonferroni gives β_σ(x) ≥ ℓ!/n − k_σ(x,x), where for x, y ∈ G and sides σ, σ'

  k_{σσ'}(x,y) := Σ_{(π,π')} P(w^σ_π = x, w^{σ'}_{π'} = y)   (pairs (π,π') on one fixed T; π ≠ π' if σ = σ').

  Below, k_σ(x,x) denotes the unordered-pair version used in Bonferroni.

**The threshold functional:**

  μ̃ := Σ_σ Σ_{x ∈ G} exp(−N_ℓ β_σ(x)),   compared with   μ := n e^{−W/n}.

Two side quantities enter the lower bounds:
- r_σ(x) := Σ P(w(S) = x), summed over reduced side-σ words w of length ≤ ℓ **with no letter occurring exactly
  once**. Words that do have such a letter are exactly uniform.
- M_ℓ := the number of such words. M_ℓ ≤ ℓ^{ℓ+1} Δ^{⌊ℓ/2⌋}, because such a word uses at most ⌊L/2⌋ distinct letters.

### Tools

**Lemma 2.1 (exact independence across supports) [PROVED].** Let T ≠ T' with |T| = |T'| = ℓ, π on T, π' on T'.
Then for all x, y ∈ G, P(w_π = x, w_{π'} = y) = 1/n², for any sides.

*Proof.* Pick i ∈ T ∖ T'. Condition on all s_j with j ≠ i. Then w_{π'} is fixed, and w_π = a s_i^{±1} b with
a, b fixed. Since s_i is uniform, P(w_π = x | rest) = 1/n. Finally w_{π'} is uniform, because each of its letters
occurs once. ∎

**Lemma 2.2 (Suen's inequality; form used here).** Let (A_i) be events with a dependency graph: every family
{A_i : i ∈ I} is independent of {A_j : j ∈ J} when there are no edges between I and J. Put
p_i = P(A_i), λ_A = Σ p_i, Λ = ½ Σ_i Σ_{j∼i} P(A_i ∩ A_j), δ = max_i Σ_{j∼i} p_j and p_max = max p_i. Then

  P(no A_i occurs) ≤ exp(−λ_A + Λ·exp((2δ + 2p_max)/(1 − p_max))).

*Source.* This is Suen (1990) as sharpened by Janson (1998). It is derived here from the form in Yadin (2009, §2),
which `LITERATURE.md` lists as verified: P(no A_i) ≤ e^{Λ'} Π(1 − p_i), with
Λ' = ½ Σ_i Σ_{j∼i} P(A_iA_j) Π_{k∼{i,j}}(1 − p_k)^{−1}. To get the displayed form, bound the product by
exp((2δ + 2p_max)/(1 − p_max)) and use Π(1 − p_i) ≤ e^{−λ_A}.

Janson's own statement, exp(−λ + Λe^{2δ}), was not re-read from the paper (see LITERATURE.md, item 14). Every
argument below only needs Λ·O(1) when δ, p_max ≤ 1/4.

**Lemma 2.3 (Lovász Local Lemma, lower-bound form).** Same dependency setting. If there are y_i ∈ [0,1) with
p_i ≤ y_i Π_{j∼i}(1 − y_j), then P(no A_i) ≥ Π(1 − y_i). (Erdős–Lovász 1975; Alon–Spencer, Lemma 5.1.1.)

**Dependency graph used throughout.** An event determined by (s_i)_{i ∈ U} gets the index U. Two indices are
joined iff their sets intersect. The letters are independent, so this is a dependency graph in the strong sense.

### Theorem 3 (per-target law) [PROVED, for every finite group]

Let X^σ_x be the number of side-σ words of length ≤ ℓ with the binding parity and value x. Assume
ℓ²λ*/Δ ≤ 1/8 and ℓ!/n ≤ 1/8.

**(a) Upper bound, for all x and σ:**

  P(X^σ_x = 0) ≤ exp(−N_ℓ β_σ(x) + ε₁),   ε₁ := 2ℓ²λ*²/Δ.

*Proof.* Keep only the events B_T := B^σ_{T,x} for |T| = ℓ. Dropping events can only increase P(no event).
- λ_A = N_ℓ β_σ(x), by definition of β.
- Each T meets at most ℓ·C(Δ−1,ℓ−1) = (ℓ²/Δ)N_ℓ other ℓ-sets T'.
- For such T' ≠ T, P(B_T ∩ B_{T'}) ≤ Σ_{π,π'} P(w_π = x = w_{π'}) = (ℓ!)²/n², by Lemma 2.1.
- So Λ ≤ ½ N_ℓ (ℓ²N_ℓ/Δ)(ℓ!)²/n² = ℓ²λ*²/(2Δ), δ ≤ ℓ²λ*/Δ ≤ 1/8 and p_max ≤ ℓ!/n ≤ 1/8.

Then Lemma 2.2 gives the claim, since e^{(1/4+1/4)/(7/8)} < 4. ∎

**(b) Lower bound, for x with s(x) := ℓ²λ/Δ + r_σ(x) ≤ 1/5:**

  P(X^σ_x = 0) ≥ exp(−N_ℓ β_σ(x) − ε₂(x)),   ε₂(x) := 6 λ s(x) + (W − W*)/n + r_σ(x).

*Proof.*
1. For every U ⊆ [Δ] with 1 ≤ |U| ≤ ℓ, let C_U = {some reduced side-σ word with support exactly U has value x}.
   Then {X^σ_x = 0} = ∩_U C_U^c. For |U| = ℓ, C_U = B_U, because a word of length ≤ ℓ with ℓ distinct letters is a
   distinct-letter word of length ℓ.
2. Put p_U = P(C_U) and q_U = Σ_{supp w = U} P(w = x) ≥ p_U.
3. Neighbourhood sum. A reduced word of length L containing a given letter can be chosen in at most
   L(Δ−1)^{L−1} = (L/Δ)W_L ways. Summing over the letters of U and over L gives
   Σ_{U'∩U≠∅} q_{U'} ≤ ℓ²λ/Δ + r_σ(x) = s(x).
4. Take y_U = (1 + 2s)p_U. Then Π_{U'∼U}(1 − y_{U'}) ≥ 1 − (1 + 2s)s ≥ 1/(1 + 2s) for s ≤ 1/5, so Lemma 2.3 applies.
5. It gives P ≥ Π(1 − y_U) ≥ exp(−(1 + 2s)(1 + 2y_max) Σ_U p_U).
6. Here Σ_U p_U ≤ N_ℓβ_σ(x) + Σ_{|U|<ℓ} q_U, and Σ_{|U|<ℓ} q_U ≤ (W − W*)/n + r_σ(x). The words counted are the
   W − W* reduced words that are not distinct-letter words of length ℓ.
7. Use N_ℓβ ≤ λ* ≤ λ and y_max ≤ s for n large. ∎

**Facts used for the asymptotics.**
- W − W* ≤ (ℓ²/Δ)W for Δ ≥ 4. Indeed W_ℓ − W* ≤ W_ℓ·C(ℓ−1,2)/(Δ−1), and the shorter words number at most
  W_ℓ/((Δ−1)² − 1).
- So with D fixed and ℓ²λ²/Δ → 0: ε₁ → 0, (W − W*)/n → 0 and λ* = λ − o(1). Also ε₂(x) → 0 whenever
  λ·r_σ(x) → 0.

In the regime that matters, n ≤ W ≤ n ln n, so Δ ≍ (n ln n)^{1/ℓ}, and the condition ℓ²λ²/Δ → 0 holds
automatically.

### Theorem 4 (threshold for every group) [PROVED]

Fix D ≥ 3 and let n → ∞ with n ≤ W ≤ n ln n. Let 𝒯 := {(x,σ) : r_σ(x) ≤ (ln n)^{−2}}. Then:

1. **1-statement:** P(diam H(G,S) > D) ≤ e^{o(1)}·μ̃. Hence diam ≤ D whp if μ̃ → 0.
2. **Exceptional set is small:** |(G × sides) ∖ 𝒯| ≤ 2M_ℓ(ln n)² = O(n^{1/2}(ln n)^{5/2}) = o(n).
3. **0-statement:** with μ̃(𝒯) := Σ_{(x,σ)∈𝒯} e^{−N_ℓβ_σ(x)}, if μ̃(𝒯)/ln n → ∞ then P(diam ≤ D) → 0.

The upper bound W ≤ n ln n can be dropped in item 1, because H(G,S') ⊆ H(G,S) for S' ⊆ S. If λ* is large, apply
item 1 to the first Δ' letters, with Δ' chosen so that λ*(Δ') ≈ 2ℓ! ln n.

*Proof of item 1.* Union bound over (x,σ) and Theorem 3(a).

*Proof of item 2.* Σ_x r_σ(x) = M_ℓ, so at most M_ℓ(ln n)² targets per side have r_σ(x) > (ln n)^{−2}. Moreover
(Δ−1)^ℓ ≤ W ≤ n ln n gives M_ℓ = O((n ln n)^{1/2}).

*Proof of item 3 (second moment).*
1. Let U = Σ_{(x,σ)∈𝒯} 1[X^σ_x = 0] and p_x := P(X^σ_x = 0).
2. On 𝒯, s(x) → 0 and λ s(x) → 0, so Theorem 3 gives p_x = e^{−N_ℓβ_σ(x) + o(1)}, uniformly.
   Hence E U = e^{o(1)} μ̃(𝒯) → ∞.
3. Pairs. For (x,σ) ≠ (y,σ'), apply Lemma 2.2 to the union of the two families {B^σ_{T,x}} and {B^{σ'}_{T,y}},
   with |T| = ℓ. Index (T,x) and (T',y) are adjacent iff T ∩ T' ≠ ∅; this includes T = T'.
   - Pairs with T ≠ T' contribute at most ℓ²λ*²/Δ = o(1) in total, by Lemma 2.1.
   - Pairs with T = T' contribute at most N_ℓ·k_{σσ'}(x,y).
   - So P(both) ≤ p_x p_y exp(o(1) + 4N_ℓ k_{σσ'}(x,y)).
4. Fix τ = τ_n → 0. A pair is *bad* if N_ℓ k_{σσ'}(x,y) > τ.
   - Good pairs contribute at most e^{o(1)+4τ}(E U)².
   - For fixed (x,σ), Σ_{(y,σ')} k_{σσ'}(x,y) ≤ 2(ℓ!)²P(w_π = x) = 2(ℓ!)²/n. So the number of bad partners of
     (x,σ) is at most 2N_ℓ(ℓ!)²/(nτ) = 2ℓ!λ*/τ.
   - Bad pairs therefore contribute at most Σ p_x·2ℓ!λ*/τ = (2ℓ!λ*/τ)·E U.
5. Hence Var U/(E U)² ≤ 1/E U + (e^{o(1)+4τ} − 1) + 2ℓ!λ*/(τ E U).
6. Choose τ = (ln n/μ̃(𝒯))^{1/2} → 0. All three terms tend to 0, because λ* ≤ ln n and μ̃(𝒯)/ln n → ∞.
7. Chebyshev gives P(U = 0) → 0, and U > 0 means diam > D by Lemma 0.1. ∎

*No hypothesis on G is used anywhere in Theorems 3–4.* The group enters only through β_σ(x), the
one-support coincidence profile, and through the set 𝒯.

**Corollary 4.1 (the generic answer).**
- **For every group:** P(diam ≤ D) → 0 if μ := n e^{−W/n} satisfies μ/ln n → ∞.
- **If moreover** β_σ(x) = (ℓ!/n)(1 − o(1/ln n)) for all (x,σ) outside a set E with Σ_E e^{−N_ℓβ} → 0, then
  P(diam ≤ D) → 1 if μ → 0.

In terms of W, the threshold is W = n ln n, with a window of width O(n ln ln n).

*Proof.* 0-statement: β ≤ ℓ!/n always, so μ̃(𝒯) ≥ |𝒯|e^{−λ*} ≥ (1 − o(1))μ, by Theorem 4 item 2 and λ* ≤ λ.
1-statement: off E, N_ℓβ = λ* − o(1) = λ − o(1), so μ̃ ≤ (number of sides)·(1 + o(1))μ + o(1). ∎

For odd D, μ̃ counts x and x^{−1} separately, and those two events coincide. The *Poisson* mean of the number
of missed targets is μ = n e^{−W/n} (n/2 inverse pairs per side, two sides), as in SIZE_LAW §2.3.4. The threshold
statement above does not depend on this factor of 2.

**Corollary 4.2 (universal window) [PROVED].** For every finite group and fixed D ≥ 3:
- (i) diam ≤ D whp once W ≥ (1 + ε)·(D−1)!·n ln n, because β ≥ 1/n gives μ̃ ≤ 2n·e^{−λ*/ℓ!};
- (ii) diam > D whp once W ≤ n(ln n − ln ln n − ω_n) with ω_n → ∞, because β ≤ ℓ!/n gives
  μ̃(𝒯) ≥ |𝒯|e^{−λ*} ≥ (1 − o(1))μ.

So **every** group has its random-Haar threshold between n ln n and (D−1)!·n ln n words. (ii) is item (c) of the
assignment, slightly stronger: it holds already at W = (1 − o(1)) n ln n, not only below (1 − ε) n ln n.

---

## 3. What β looks like: special targets and coincidences

β_σ(x) < ℓ!/n exactly when distinct arrangements can coincide at x. Four mechanisms are exact, two give
first-order losses. All are visible in the data (DATA_CHECK.md §4–§6).

1. **Inverse pairs (D odd) [PROVED].** For an A-word, w_π^{−1} = w_{rev π} is again an arrangement on the same
   support and side. So {w_π = x} = {w_{rev π} = x^{−1}}, and x, x^{−1} are missed together. For an **involution** t
   (t² = e ≠ t), arrangements pair up: β_σ(t) ≤ (ℓ!/2)/n.
2. **Central targets (D odd) [PROVED].** If z is central, w_π = z forces every cyclic rotation of w_π by 2 letters
   to equal z, since a rotation is a conjugate. A rotation by 1 letter turns an A-word into a B-word, so the A and B
   events for z coincide. Rotation orbits of distinct-letter words have size exactly k = ℓ/2, so
   β_σ(z) ≤ (ℓ!/k)/n. If moreover z² = e, then β_σ(z) ≤ (ℓ!/2k)/n = (ℓ−1)!/n.
   For D even (odd ℓ), no rotation or inversion preserves the sign pattern, and central targets are not special.
3. **Abelian groups [PROVED].** All sign-preserving rearrangements coincide (Theorem 2), so
   β_σ(x) ≤ C(ℓ, ⌈ℓ/2⌉)/n.
4. **Q × Z_m, or small G' in general.** Sign-preserving rearrangements agree in G/G'. They coincide in G with
   probability about 1/|G'|, against 1/n for unrelated words.
   - First-order loss: a fraction ≈ (R̄_ℓ − 1)/(2|G'|) of all words, where R̄_ℓ is the mean number of reduced
     sign-preserving rearrangements: 3.4 at (Δ,ℓ) = (11,4), 47 at (8,7), 250 at (13,8), 645 at (10,9).
   - This is why small-Q × large-cyclic groups are bad. For SL(2,8)×Z₂₁₁ it predicts an excess factor ≈ 1.5;
     SIZE_LAW measured ≈ 8. **[heuristic]**
5. **Junction swaps (involution density).** If s_a s_b^{−1} is an involution, then s_a s_b^{−1} = s_b s_a^{−1}, so
   swapping two adjacent letters does not change the value. Each junction of a word is such a coincidence with
   probability τ = I(G)/(n−1), where I(G) is the number of involutions. A word of length L therefore loses a
   fraction ≈ (L−1)τ/2. **[heuristic, first order]**
   This is the dominant effect for PSL(2,q) with small q: τ ≈ 1/12 for PSL(2,11)×Z₂. The model reproduces the
   Monte Carlo at D = 4, 5 and 6 (DATA_CHECK §6).
6. **The rest.** In quasirandom groups every other pair of distinct arrangements coincides with probability
   O_ℓ(1/q) (Lemma 5.1), which is negligible.

`scripts/model.py` puts mechanisms 1, 2, 4 and 5 into one Poisson mean:

- generic targets: (n − |Z| − I_nc)·e^{−W_eff/n};
- non-central involutions: 2·I_nc·e^{−W_eff/(2n)};
- central non-involutions: ½(|Z| − 1 − I_c)·e^{−ρ};
- central involutions: I_c·e^{−ρ/2};

where ρ = (W_eff/W)·Σ_{j≤k} W_{2j}/(jn), I_c and I_nc count central and non-central involutions, and W_eff is W
minus the first-order coincidence losses.

### Consequences

**Corollary 5.2 (PSL and PGL at odd D) [PROVED].** Let G = PSL(2,q) (q odd) or PGL(2,q), and D odd fixed. Then
P(diam ≤ D) → 0 whenever W ≤ (4/3 − ε)·n ln n.

*Proof.*
- G has at least q(q−1)/2 ≥ c·n^{2/3} involutions, in at most two conjugacy classes, each of size ≥ q(q−1)/2.
- β is a class function, so P(w = t) ≤ 1/|cl(t)| for any word w. Hence r_σ(t) ≤ 2M_ℓ/(q(q−1)) = O(n^{−1/6}(ln n)^{1/2}),
  and all involutions lie in 𝒯.
- By mechanism 1, N_ℓβ_σ(t) ≤ λ*/2. So μ̃(𝒯) ≥ c·n^{2/3}·e^{−λ*/2} ≥ c·n^{2/3 − (2/3 − ε/2)} = c·n^{ε/2}, which is
  ≫ ln n.
- Apply Theorem 4, item 3. ∎

For SL(2,q), the only involution is −I, and this obstruction disappears. More generally, if I(G) ≥ n^a with
a > 1/2, the odd-D threshold is at least 2a·n ln n. The data show the effect directly. The screening order at
(6,9), N = 58,752, is SL < PSL×Z₂₄ < PGL < PSL(2,49), and the model predicts its size. No pure PSL or PGL group
holds an odd-D record. The PSL(2,29)×Z₁₇ wall at (7,9) is explained too (DATA_CHECK §4).

**Corollary 5.3 (abelian groups) [PROVED].** For abelian G and D even fixed, P(diam ≤ D) → 0 whenever
W ≤ (1 − ε)·⌈ℓ/2⌉!⌊ℓ/2⌋!·n ln n. Examples: twice n ln n at D = 4, and 12 times at D = 6.

*Proof.* By mechanism 3, μ̃(𝒯) ≥ |𝒯|·exp(−λ*/(⌈ℓ/2⌉!⌊ℓ/2⌋!)). ∎

Christofides and Markström found the same phenomenon for random Cayley graphs at diameter 2: the threshold constant
depends on the group, being 2 for Z_2^n, 1/2 for cyclic groups and 1/4 for symmetric groups. See LITERATURE.md.

### SL(2,q): what is proved and what is missing

**Lemma 5.1 (SL(2,q) short-word fibres) [PROVED, cited input].** Fix L. There is C_L such that for every
nontrivial reduced word u of length ≤ L and every prime power q,

  P_S(u(S) = e) ≤ C_L/q   in SL(2,q).

*Proof.* Let u involve r ≤ L letters. The set {u = e} ⊂ SL_2^r is a closed subvariety. It is proper, since u is not
the identity on SL_2(\bar F_q) (Borel 1983: word maps on semisimple groups are dominant). So its dimension is
≤ 3r − 1. Its degree is bounded by a function of L, by Bézout applied to the 4 entry equations of degree ≤ L and
the r determinant equations. A variety V of dimension d has |V(F_q)| ≤ deg(V)·q^d. Divide by |SL_2(F_q)|^r ≍ q^{3r}.

Cited input: Borel's dominance theorem, and the elementary point-count bound (e.g. via Lang–Weil 1954). The uniform
degree bound is standard; I did not write out the elimination. ∎

Applied to u = w_π^{−1}w_{π'}, Lemma 5.1 gives ρ_ℓ := max_{π≠π'} P(w_π = w_{π'}) ≤ C_ℓ/q. Hence
Σ_x N_ℓ k(x,x) = O(ln n · ℓ! /q) → 0.

**Gap G1.** Corollary 4.1 for SL(2,q) needs the *pointwise* bound

  P(w_π = x = w_{π'}) ≤ C_ℓ/(q·n)   for all non-central x and all π ≠ π'.

Then n k(x,x)·λ*/ℓ! = O(ℓ! ln n/q) → 0, and the central targets ±I go into E using β ≥ 1/n. Lemma 5.1 only gives
the average over x of this quantity.

- G1 can be checked by hand for the coincidence types that occur most often:
  - junction swaps: (ab^{−1})² = e forces b = ±a, so P ≤ 2/n²;
  - reversals: P = |C(x)|/n², and |C(x)| ≤ 2(q+1) for non-central x;
  - rotations: P = |C(x)|/n² as well.
- In general, G1 is the statement that the coincidence variety {w_π = w_{π'}} ⊂ SL_2^ℓ has no component of
  dimension 3ℓ − 1 on which tr w_π is constant. It looks like a dominance statement for word maps with constants,
  of the kind studied by Gordeev–Kunyavskii–Plotkin; I have not proved it.
- So: **for SL(2,q), the 0-statement (diam > D whp when μ/ln n → ∞) is proved, and the 1-statement (diam ≤ D whp
  when μ → 0) is [SKETCH, gap G1].** The Monte Carlo agrees with the 1-statement (DATA_CHECK §6).

---

## 4. The records' regime: Δ fixed, D → ∞

**Conjecture 6 [CONJECTURE].** Fix Δ ≥ 3. Let G = SL(2,q), q → ∞, S uniform random, and let μ_D := n e^{−W(Δ,D)/n}
(with the §3 corrections for odd D). Then P(diam H(G,S) ≤ D) → 1 if μ_D → 0 and → 0 if μ_D → ∞. Equivalently,
whp

  diam H(G,S) = min{D : W(Δ,D) ≥ n ln n + ω_n n} = log_{Δ−1} n + log_{Δ−1} ln n + O(1),

and the order at diameter D is N = Δ g_Δ (Δ−1)^{D−2} / ln(N/μ) · (1 + o(1)), with μ = O(1) at success
probability bounded away from 0 and 1.

**What is known for fixed Δ** (LITERATURE.md):
- diam ≥ log_{Δ−1} n − O(1) for every S (Theorem 1).
- diam ≤ C log n for random S when q = p is prime, from Bourgain–Gamburd expansion.
- diam ≤ (log p)^c for every generating set (Helfgott).
- Girth ≥ (1/3 − o(1))·log_{Δ−1} n (Gamburd–Hoory–Shahshahani–Shalev–Virág).

Nothing in the literature reaches the constant 1 in front of log_{Δ−1} n, let alone the log log term.

**Gap G2: why the proof of §2 does not extend.**
- With Δ fixed, every pair of words shares letters. The dependency graph of §2 is complete, so δ ≈ λ ≈ ln n, and
  both Suen and the LLL lose a constant factor in the exponent.
- The method of moments needs approximate K-wise independence of word values for K up to ≈ e·ln n. That is
  **false** for K > Δ: the probability space has only n^Δ points, so a nonempty event has probability ≥ n^{−Δ},
  while independence would predict n^{−K}.
- So a proof needs a genuinely different argument. Two candidates:
  - a martingale over the BFS levels: expose the ball level by level, with SIZE_LAW §2.3.1 as evidence that the
    levels grow like a random process;
  - pseudo-randomness of the *last* level, conditional on the ball of radius ℓ − 1.

  I could not do either.

**Evidence for Conjecture 6.**
- The Monte Carlo at Δ = 7–14 (DATA_CHECK §6) is far outside Theorem 3's quantitative range (ε₁ ≫ 1 there). It
  still matches e^{−μ} with the §3 corrections to within sampling error and a 10–20 % excess.
- One additional failure mode appears at small Δ: P(fail) ≈ 3–13 % at μ ≈ 0, from atypical S.
- The records follow N ≈ W/ln(N/μ*) to 2 % (DATA_CHECK §3).

---

## 5. How this explains the size law

1. **The log factor (Kenan's hunch) is right.** At the threshold W/n = ln(n/μ). With
   W = Δ g_Δ (Δ−1)^{D−2}(1 + O(Δ^{−2})), this gives C_D = Δ g_Δ / ln(N/μ).
   - It is a theorem in the D-fixed regime (Corollary 4.1, for groups with few coincidences).
   - It is Conjecture 6 in the fixed-Δ regime.
   - Since ln N ≈ (D−2) ln(Δ−1), C_D falls like Δ/(D ln(Δ−1)). There is **no** constant c with
     N ≥ c(Δ−1)^{D−2} along random Haar graphs (SIZE_LAW §5(i)).
2. **The exact normalisation** is C_D·ln(N/μ)/(Δ g_Δ) = 1, not C_D·ln N = const.
   - For a single random S at success probability 1 − p, μ = ln(1/(1−p)). For p = 1/2 that is μ = ln 2.
   - Our records are best-of-many searches and sit at μ* ≈ 4–40 (DATA_CHECK §2–3).
3. **Best of T tries.** If one random S succeeds with probability ≈ e^{−μ}, then T independent tries reach
   μ* ≈ ln T. Annealing does better: SIZE_LAW's capability rule μ_max = 13 + 2 ln(M/10^5) means M evaluations act
   like T ≈ (M/150)² independent samples. The search threshold is therefore

     N_T = Δ g_Δ (Δ−1)^{D−2} / ln(N_T/μ*),   μ* = μ_max(M),   M ∝ budget/N.

   A fixed budget makes μ* fall like −2 ln N, which is the residual drift. DATA_CHECK §3 fits one budget,
   ≈ 700 core-seconds per order, and gets rms 2.0 % over 27 cells with no D-trend.
4. **Group choice** enters through β:
   - generic targets give the main term;
   - special targets (odd D: involutions and centre) and coincidence losses (small G', many involutions) give
     corrections;
   - SL(2,q) × small Z_m minimises all of them. That is what the screening found empirically.

---

## 6. Status summary

| statement | status |
|---|---|
| Lemma 0.1 covering lemma (both directions) | PROVED (sufficiency also in Lean) |
| Thm 1: n ≤ W(Δ,D) = bipartite Moore bound per side, any S | PROVED |
| Thm 2: abelian bound \|G/G'\| ≤ A(Δ,D) = O(D^{Δ−1}) | PROVED |
| Thm 3: per-target law P(x missed) = exp(−C(Δ,D−1)β(x) ± o(1)), any finite G, D fixed | PROVED (Suen in the form derived from Yadin's statement) |
| Thm 4: 1-statement μ̃ → 0 and 0-statement μ̃(𝒯)/ln n → ∞, any finite G | PROVED |
| Cor 4.1 (0-part) and Cor 4.2: every group's threshold lies in [n ln n, (D−1)! n ln n]; diam > D whp below n(ln n − ln ln n − ω) | PROVED |
| Cor 5.2: PSL(2,q), PGL(2,q), odd D need ≥ (4/3) n ln n | PROVED |
| Cor 5.3: abelian, even D need ≥ ⌈ℓ/2⌉!⌊ℓ/2⌋! n ln n | PROVED |
| Lemma 5.1: SL(2,q) coincidence probability ≤ C/q | PROVED, cited input (Borel; point counting) |
| SL(2,q), D fixed: diam > D whp if μ/ln n → ∞ | PROVED |
| SL(2,q), D fixed: diam ≤ D whp if μ → 0 (constant 1) | SKETCH, gap G1 |
| Full Poisson limit P(diam ≤ D) → e^{−μ} inside the window | not proved (needs factorial moments; same bookkeeping as Thm 4 plus G1) |
| Δ fixed, D → ∞ (records' regime) | CONJECTURE 6; obstacle G2 |
| First-order coincidence model (junction swaps, rearrangements) | heuristic, tested numerically |
