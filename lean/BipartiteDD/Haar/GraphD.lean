import BipartiteDD.Haar.Graph
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Tactic.Group

/-! Diameter of Haar graphs for every diameter, from covering by words.

For `S ⊆ G` the Haar graph has `inl g` (the `A` side) and `inr h` (the `B` side), with
`inl g ~ inr h` iff `h * g⁻¹ ∈ S`. Two `A`-steps `inl x – inr (t * x) – inl (s⁻¹ * t * x)` move `x` to
`s⁻¹ * t * x`, and two `B`-steps `inr x – inl (b⁻¹ * x) – inr (a * b⁻¹ * x)` move `x` to `a * b⁻¹ * x`.
So a product of `n` left factors `s⁻¹ * t` gives an `A`-to-`A` walk of length `2 n`, and a product of
`n` right factors `a * b⁻¹` gives a `B`-to-`B` walk of length `2 n`.

* Odd `D = 2n + 1`: both sides are covered by products of `n` factors (`haar_ediam_le_odd`).
* Even `D = 2n + 2`: every `x` is `s * y` with `s ∈ S` and `y` a product of `n` left factors, that is
  `2n + 1` letters `s, s⁻¹, …` alternately. This is the even-`D` criterion of `research/frontier/PLAN.md`
  (`D - 1` letters). Only the direction "covering ⇒ diameter" is proved here (`haar_ediam_le_even`).

The certificate section replaces "for all `x`, some word" by a `Bool` check over explicit index words, which
`decide +kernel` evaluates without enumerating the words. -/

namespace BipartiteDD.Haar

open SimpleGraph

variable {G : Type*} [Group G] {S : Finset G}

/-- `x` is a product of at most `n` factors `s⁻¹ * t`, with `s, t ∈ S`. Words are lists of pairs `(s, t)`. -/
def IsLeftWord (S : Finset G) (n : ℕ) (x : G) : Prop :=
  ∃ w : List (G × G), w.length ≤ n ∧ (∀ p ∈ w, p.1 ∈ S ∧ p.2 ∈ S) ∧
    (w.map fun p => p.1⁻¹ * p.2).prod = x

/-- `x` is a product of at most `n` factors `a * b⁻¹`, with `a, b ∈ S`. Words are lists of pairs `(a, b)`. -/
def IsRightWord (S : Finset G) (n : ℕ) (x : G) : Prop :=
  ∃ w : List (G × G), w.length ≤ n ∧ (∀ p ∈ w, p.1 ∈ S ∧ p.2 ∈ S) ∧
    (w.map fun p => p.1 * p.2⁻¹).prod = x

/-! ### One step and two steps -/

theorem adj_inl_inr_mul {s : G} (hs : s ∈ S) (g : G) :
    (haarGraph S).Adj (.inl g) (.inr (s * g)) := by
  rw [haarGraph_adj_inl_inr, mul_inv_cancel_right]
  exact hs

theorem adj_inr_inl_inv_mul {s : G} (hs : s ∈ S) (h : G) :
    (haarGraph S).Adj (.inr h) (.inl (s⁻¹ * h)) := by
  rw [haarGraph_adj_inr_inl]
  have e : h * (s⁻¹ * h)⁻¹ = s := by group
  rw [e]
  exact hs

theorem edist_inl_inl_le_two {s t : G} (hs : s ∈ S) (ht : t ∈ S) (x : G) :
    (haarGraph S).edist (.inl x) (.inl (s⁻¹ * t * x)) ≤ 2 := by
  have h1 : (haarGraph S).Adj (.inl x) (.inr (t * x)) := adj_inl_inr_mul ht x
  have h2 : (haarGraph S).Adj (.inr (t * x)) (.inl (s⁻¹ * t * x)) := by
    rw [haarGraph_adj_inr_inl]
    have e : t * x * (s⁻¹ * t * x)⁻¹ = s := by group
    rw [e]
    exact hs
  exact (edist_le (Walk.cons h1 (Walk.cons h2 Walk.nil))).trans (by norm_num)

theorem edist_inr_inr_le_two {a b : G} (ha : a ∈ S) (hb : b ∈ S) (x : G) :
    (haarGraph S).edist (.inr x) (.inr (a * b⁻¹ * x)) ≤ 2 := by
  have h1 : (haarGraph S).Adj (.inr x) (.inl (b⁻¹ * x)) := adj_inr_inl_inv_mul hb x
  have h2 : (haarGraph S).Adj (.inl (b⁻¹ * x)) (.inr (a * b⁻¹ * x)) := by
    rw [haarGraph_adj_inl_inr]
    have e : a * b⁻¹ * x * (b⁻¹ * x)⁻¹ = a := by group
    rw [e]
    exact ha
  exact (edist_le (Walk.cons h1 (Walk.cons h2 Walk.nil))).trans (by norm_num)

/-! ### Walks along words -/

/-- A left word of `n` factors gives an `A`-to-`A` walk of length at most `2 n`. -/
theorem edist_inl_le_word {w : List (G × G)} (hw : ∀ p ∈ w, p.1 ∈ S ∧ p.2 ∈ S) (g : G) :
    (haarGraph S).edist (.inl g) (.inl ((w.map fun p => p.1⁻¹ * p.2).prod * g))
      ≤ ((2 * w.length : ℕ) : ENat) := by
  induction w generalizing g with
  | nil => simp
  | cons p w ih =>
    obtain ⟨hp1, hp2⟩ := hw p (List.mem_cons_self)
    have hrest : ∀ q ∈ w, q.1 ∈ S ∧ q.2 ∈ S := fun q hq => hw q (List.mem_cons_of_mem _ hq)
    have h1 := ih hrest g
    have h2 := edist_inl_inl_le_two (s := p.1) (t := p.2) hp1 hp2
      ((w.map fun p => p.1⁻¹ * p.2).prod * g)
    rw [List.map_cons, List.prod_cons, mul_assoc]
    calc (haarGraph S).edist (.inl g) (.inl (p.1⁻¹ * p.2 * ((w.map fun p => p.1⁻¹ * p.2).prod * g)))
        ≤ (haarGraph S).edist (.inl g) (.inl ((w.map fun p => p.1⁻¹ * p.2).prod * g)) +
          (haarGraph S).edist (.inl ((w.map fun p => p.1⁻¹ * p.2).prod * g))
            (.inl (p.1⁻¹ * p.2 * ((w.map fun p => p.1⁻¹ * p.2).prod * g))) :=
          SimpleGraph.edist_triangle
      _ ≤ ((2 * w.length : ℕ) : ENat) + 2 := add_le_add h1 h2
      _ = ((2 * (w.length + 1) : ℕ) : ENat) := by push_cast; ring

/-- A right word of `n` factors gives a `B`-to-`B` walk of length at most `2 n`. -/
theorem edist_inr_le_word {w : List (G × G)} (hw : ∀ p ∈ w, p.1 ∈ S ∧ p.2 ∈ S) (h : G) :
    (haarGraph S).edist (.inr h) (.inr ((w.map fun p => p.1 * p.2⁻¹).prod * h))
      ≤ ((2 * w.length : ℕ) : ENat) := by
  induction w generalizing h with
  | nil => simp
  | cons p w ih =>
    obtain ⟨hp1, hp2⟩ := hw p (List.mem_cons_self)
    have hrest : ∀ q ∈ w, q.1 ∈ S ∧ q.2 ∈ S := fun q hq => hw q (List.mem_cons_of_mem _ hq)
    have h1 := ih hrest h
    have h2 := edist_inr_inr_le_two (a := p.1) (b := p.2) hp1 hp2
      ((w.map fun p => p.1 * p.2⁻¹).prod * h)
    rw [List.map_cons, List.prod_cons, mul_assoc]
    calc (haarGraph S).edist (.inr h) (.inr (p.1 * p.2⁻¹ * ((w.map fun p => p.1 * p.2⁻¹).prod * h)))
        ≤ (haarGraph S).edist (.inr h) (.inr ((w.map fun p => p.1 * p.2⁻¹).prod * h)) +
          (haarGraph S).edist (.inr ((w.map fun p => p.1 * p.2⁻¹).prod * h))
            (.inr (p.1 * p.2⁻¹ * ((w.map fun p => p.1 * p.2⁻¹).prod * h))) :=
          SimpleGraph.edist_triangle
      _ ≤ ((2 * w.length : ℕ) : ENat) + 2 := add_le_add h1 h2
      _ = ((2 * (w.length + 1) : ℕ) : ENat) := by push_cast; ring

/-! ### Odd diameter `2n + 1` -/

/-- Odd diameter: if both sides are covered by products of `n` factors, the Haar graph of `S` has
diameter at most `2 n + 1`. The hypothesis `hS` is needed for the `A`-to-`B` step when `n = 0`. -/
theorem haar_ediam_le_odd (hS : S.Nonempty) (n : ℕ)
    (hA : ∀ x : G, IsLeftWord S n x) (hB : ∀ x : G, IsRightWord S n x) :
    (haarGraph S).ediam ≤ ((2 * n + 1 : ℕ) : ENat) := by
  -- `A` to `A` and `B` to `B` within `2 n`
  have aa : ∀ g g' : G, (haarGraph S).edist (.inl g) (.inl g') ≤ ((2 * n : ℕ) : ENat) := by
    intro g g'
    obtain ⟨w, hwn, hw, hx⟩ := hA (g' * g⁻¹)
    have h := edist_inl_le_word hw g
    rw [hx, inv_mul_cancel_right] at h
    exact h.trans (by exact_mod_cast (show 2 * w.length ≤ 2 * n by omega))
  have bb : ∀ h h' : G, (haarGraph S).edist (.inr h) (.inr h') ≤ ((2 * n : ℕ) : ENat) := by
    intro h h'
    obtain ⟨w, hwn, hw, hx⟩ := hB (h' * h⁻¹)
    have e := edist_inr_le_word hw h
    rw [hx, inv_mul_cancel_right] at e
    exact e.trans (by exact_mod_cast (show 2 * w.length ≤ 2 * n by omega))
  -- `A` to `B` within `2 n + 1`: one step to `inr (s * g)`, then `B` to `B`
  have ab : ∀ g h : G, (haarGraph S).edist (.inl g) (.inr h) ≤ ((2 * n + 1 : ℕ) : ENat) := by
    intro g h
    obtain ⟨s, hs⟩ := hS
    have h1 : (haarGraph S).edist (.inl g) (.inr (s * g)) ≤ 1 :=
      (edist_le (Walk.cons (adj_inl_inr_mul hs g) Walk.nil)).trans (by norm_num)
    calc (haarGraph S).edist (.inl g) (.inr h)
        ≤ (haarGraph S).edist (.inl g) (.inr (s * g)) +
          (haarGraph S).edist (.inr (s * g)) (.inr h) := SimpleGraph.edist_triangle
      _ ≤ 1 + ((2 * n : ℕ) : ENat) := add_le_add h1 (bb _ _)
      _ = ((2 * n + 1 : ℕ) : ENat) := by push_cast; ring
  rw [ediam_le_iff]
  intro u v
  rcases u with g | g <;> rcases v with g' | g'
  · exact (aa g g').trans (by exact_mod_cast (show 2 * n ≤ 2 * n + 1 by omega))
  · exact ab g g'
  · rw [SimpleGraph.edist_comm]
    exact ab g' g
  · exact (bb g g').trans (by exact_mod_cast (show 2 * n ≤ 2 * n + 1 by omega))

/-! ### Even diameter `2 n + 2` -/

/-- Even diameter: if every `x` is `s * y` with `s ∈ S` and `y` a product of `n` left factors, the
Haar graph of `S` has diameter at most `2 n + 2`. -/
theorem haar_ediam_le_even (n : ℕ) (hA : ∀ x : G, ∃ s ∈ S, IsLeftWord S n (s⁻¹ * x)) :
    (haarGraph S).ediam ≤ ((2 * n + 2 : ℕ) : ENat) := by
  -- `A` to `B` within `2 n + 1`: walk to `inl y`, where `s * y = x`, then one step to `inr (x * g)`
  have ab : ∀ g h : G, (haarGraph S).edist (.inl g) (.inr h) ≤ ((2 * n + 1 : ℕ) : ENat) := by
    intro g h
    obtain ⟨s, hs, w, hwn, hwS, hwp⟩ := hA (h * g⁻¹)
    have h1 := edist_inl_le_word hwS g
    rw [hwp] at h1
    have h1' : (haarGraph S).edist (.inl g) (.inl (s⁻¹ * (h * g⁻¹) * g)) ≤ ((2 * n : ℕ) : ENat) :=
      h1.trans (by exact_mod_cast (show 2 * w.length ≤ 2 * n by omega))
    have h2 : (haarGraph S).Adj (.inl (s⁻¹ * (h * g⁻¹) * g)) (.inr h) := by
      have := adj_inl_inr_mul hs (s⁻¹ * (h * g⁻¹) * g)
      rwa [show s * (s⁻¹ * (h * g⁻¹) * g) = h by group] at this
    calc (haarGraph S).edist (.inl g) (.inr h)
        ≤ (haarGraph S).edist (.inl g) (.inl (s⁻¹ * (h * g⁻¹) * g)) +
          (haarGraph S).edist (.inl (s⁻¹ * (h * g⁻¹) * g)) (.inr h) := SimpleGraph.edist_triangle
      _ ≤ ((2 * n : ℕ) : ENat) + 1 :=
          add_le_add h1' ((edist_le (Walk.cons h2 Walk.nil)).trans (by norm_num))
      _ = ((2 * n + 1 : ℕ) : ENat) := by push_cast; ring
  obtain ⟨s, hs, -⟩ := hA 1
  -- `A` to `A` and `B` to `B` via one neighbour
  have aa : ∀ g g' : G, (haarGraph S).edist (.inl g) (.inl g') ≤ ((2 * n + 2 : ℕ) : ENat) := by
    intro g g'
    have h1 : (haarGraph S).edist (.inl g) (.inr (s * g)) ≤ 1 :=
      (edist_le (Walk.cons (adj_inl_inr_mul hs g) Walk.nil)).trans (by norm_num)
    have h2 : (haarGraph S).edist (.inr (s * g)) (.inl g') ≤ ((2 * n + 1 : ℕ) : ENat) := by
      rw [SimpleGraph.edist_comm]
      exact ab g' (s * g)
    calc (haarGraph S).edist (.inl g) (.inl g')
        ≤ (haarGraph S).edist (.inl g) (.inr (s * g)) +
          (haarGraph S).edist (.inr (s * g)) (.inl g') := SimpleGraph.edist_triangle
      _ ≤ 1 + ((2 * n + 1 : ℕ) : ENat) := add_le_add h1 h2
      _ = ((2 * n + 2 : ℕ) : ENat) := by push_cast; ring
  have bb : ∀ h h' : G, (haarGraph S).edist (.inr h) (.inr h') ≤ ((2 * n + 2 : ℕ) : ENat) := by
    intro h h'
    have h1 : (haarGraph S).edist (.inr h) (.inl (s⁻¹ * h)) ≤ 1 :=
      (edist_le (Walk.cons (adj_inr_inl_inv_mul hs h) Walk.nil)).trans (by norm_num)
    calc (haarGraph S).edist (.inr h) (.inr h')
        ≤ (haarGraph S).edist (.inr h) (.inl (s⁻¹ * h)) +
          (haarGraph S).edist (.inl (s⁻¹ * h)) (.inr h') := SimpleGraph.edist_triangle
      _ ≤ 1 + ((2 * n + 1 : ℕ) : ENat) := add_le_add h1 (ab _ _)
      _ = ((2 * n + 2 : ℕ) : ENat) := by push_cast; ring
  rw [ediam_le_iff]
  intro u v
  rcases u with g | g <;> rcases v with g' | g'
  · exact aa g g'
  · exact (ab g g').trans (by exact_mod_cast (show 2 * n + 1 ≤ 2 * n + 2 by omega))
  · rw [SimpleGraph.edist_comm]
    exact (ab g' g).trans (by exact_mod_cast (show 2 * n + 1 ≤ 2 * n + 2 by omega))
  · exact bb g g'

/-! ### Words for the degree-5 statement

The hypotheses of `haar_ediam_le_five` (in `Main`) are products of four factors; these lemmas turn them
into `IsLeftWord S 2` and `IsRightWord S 2`. -/

theorem isLeftWord_two_of_four {x : G}
    (h : ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, x = a⁻¹ * b * c⁻¹ * d) : IsLeftWord S 2 x := by
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := h
  refine ⟨[(a, b), (c, d)], by simp, ?_, by simp [mul_assoc]⟩
  intro p hp
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> simp [ha, hb, hc, hd]

theorem isRightWord_two_of_four {x : G}
    (h : ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, x = a * b⁻¹ * c * d⁻¹) : IsRightWord S 2 x := by
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := h
  refine ⟨[(a, b), (c, d)], by simp, ?_, by simp [mul_assoc]⟩
  intro p hp
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> simp [ha, hb, hc, hd]

/-! ### Certificates

A left certificate for a list `tgt` of targets is a list `cert` of index words: entry `i` is a list of
pairs `(i₁, j₁), …` of indices into `sL`, standing for `sL[i₁]⁻¹ * sL[j₁] * …`. `leftCertOK` checks, for every
`i < tgt.length`, that the word has at most `n` pairs, uses only indices of `sL`, and multiplies to `tgt[i]`.
It is a `Bool` computation, so `decide +kernel` checks it without enumerating any words. Together with a
numbering `idx : G → ℕ` of the group (`tgt.getD (idx x) 1 = x`), a successful check gives the covering
hypotheses. The right and even certificates work the same way. -/

theorem getD_mem {S : Finset G} {sL : List G} (hsL : ∀ s ∈ sL, s ∈ S) {i : ℕ} (hi : i < sL.length) :
    sL.getD i 1 ∈ S := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact hsL _ (List.getElem_mem hi)

/-- The index word `w` has at most `n` pairs, all indices in range for `sL`. -/
def wordOK (sL : List G) (n : ℕ) (w : List (ℕ × ℕ)) : Bool :=
  decide (w.length ≤ n) && w.all fun p => decide (p.1 < sL.length) && decide (p.2 < sL.length)

/-- The group word of an index word: each pair `(i, j)` becomes `(sL[i], sL[j])`. -/
def elemWord (sL : List G) (w : List (ℕ × ℕ)) : List (G × G) :=
  w.map fun p => (sL.getD p.1 1, sL.getD p.2 1)

theorem wordOK_length {sL : List G} {n : ℕ} {w : List (ℕ × ℕ)} (hw : wordOK sL n w = true) :
    w.length ≤ n := by
  simp only [wordOK, Bool.and_eq_true, decide_eq_true_eq] at hw
  exact hw.1

theorem mem_of_wordOK {S : Finset G} {sL : List G} {n : ℕ} {w : List (ℕ × ℕ)}
    (hw : wordOK sL n w = true) (hsL : ∀ s ∈ sL, s ∈ S) :
    ∀ q ∈ elemWord sL w, q.1 ∈ S ∧ q.2 ∈ S := by
  simp only [wordOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hw
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  exact ⟨getD_mem hsL (hw.2 p hp).1, getD_mem hsL (hw.2 p hp).2⟩

/-- Check of a left certificate: entry `i` multiplies to `tgt[i]` with factors `s⁻¹ * t`. -/
def leftCertOK [DecidableEq G] (sL tgt : List G) (n : ℕ) (cert : List (List (ℕ × ℕ))) : Bool :=
  (List.range tgt.length).all fun i =>
    wordOK sL n (cert.getD i []) &&
      decide (((elemWord sL (cert.getD i [])).map fun q => q.1⁻¹ * q.2).prod = tgt.getD i 1)

/-- Check of a right certificate: entry `i` multiplies to `tgt[i]` with factors `a * b⁻¹`. -/
def rightCertOK [DecidableEq G] (sL tgt : List G) (n : ℕ) (cert : List (List (ℕ × ℕ))) : Bool :=
  (List.range tgt.length).all fun i =>
    wordOK sL n (cert.getD i []) &&
      decide (((elemWord sL (cert.getD i [])).map fun q => q.1 * q.2⁻¹).prod = tgt.getD i 1)

/-- Check of an even certificate: entry `j` is `(i, w)` with `sL[i] * (product of w) = tgt[j]`. -/
def evenCertOK [DecidableEq G] (sL tgt : List G) (n : ℕ) (cert : List (ℕ × List (ℕ × ℕ))) : Bool :=
  (List.range tgt.length).all fun j =>
    let e := cert.getD j (0, [])
    decide (e.1 < sL.length) && wordOK sL n e.2 &&
      decide (sL.getD e.1 1 * ((elemWord sL e.2).map fun q => q.1⁻¹ * q.2).prod = tgt.getD j 1)

theorem isLeftWord_of_cert [DecidableEq G] {S : Finset G} {sL tgt : List G} {n : ℕ}
    {cert : List (List (ℕ × ℕ))} (hc : leftCertOK sL tgt n cert = true) (hsL : ∀ s ∈ sL, s ∈ S)
    (idx : G → ℕ) (hidx : ∀ x, idx x < tgt.length) (hval : ∀ x, tgt.getD (idx x) 1 = x) :
    ∀ x : G, IsLeftWord S n x := by
  intro x
  have h := List.all_eq_true.mp hc (idx x) (List.mem_range.mpr (hidx x))
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hw, hp⟩ := h
  exact ⟨elemWord sL (cert.getD (idx x) []), by simpa [elemWord] using wordOK_length hw,
    mem_of_wordOK hw hsL, hp.trans (hval x)⟩

theorem isRightWord_of_cert [DecidableEq G] {S : Finset G} {sL tgt : List G} {n : ℕ}
    {cert : List (List (ℕ × ℕ))} (hc : rightCertOK sL tgt n cert = true) (hsL : ∀ s ∈ sL, s ∈ S)
    (idx : G → ℕ) (hidx : ∀ x, idx x < tgt.length) (hval : ∀ x, tgt.getD (idx x) 1 = x) :
    ∀ x : G, IsRightWord S n x := by
  intro x
  have h := List.all_eq_true.mp hc (idx x) (List.mem_range.mpr (hidx x))
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hw, hp⟩ := h
  exact ⟨elemWord sL (cert.getD (idx x) []), by simpa [elemWord] using wordOK_length hw,
    mem_of_wordOK hw hsL, hp.trans (hval x)⟩

/-- An even certificate gives `∀ x, ∃ s ∈ S, IsLeftWord S n (s⁻¹ * x)`: `x = s * y`, `y` the word. -/
theorem isEven_of_cert [DecidableEq G] {S : Finset G} {sL tgt : List G} {n : ℕ}
    {cert : List (ℕ × List (ℕ × ℕ))} (hc : evenCertOK sL tgt n cert = true) (hsL : ∀ s ∈ sL, s ∈ S)
    (idx : G → ℕ) (hidx : ∀ x, idx x < tgt.length) (hval : ∀ x, tgt.getD (idx x) 1 = x) :
    ∀ x : G, ∃ s ∈ S, IsLeftWord S n (s⁻¹ * x) := by
  intro x
  have h := List.all_eq_true.mp hc (idx x) (List.mem_range.mpr (hidx x))
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hi, hw⟩, hp⟩ := h
  have hx := hp.trans (hval x)
  refine ⟨sL.getD (cert.getD (idx x) (0, [])).1 1, getD_mem hsL hi,
    elemWord sL (cert.getD (idx x) (0, [])).2, by simpa [elemWord] using wordOK_length hw,
    mem_of_wordOK hw hsL, ?_⟩
  exact eq_inv_mul_iff_mul_eq.mpr hx

end BipartiteDD.Haar

/-! ### A check: the Haar graph of `ℤ/5` with `S = {0, 1}` (the 10-cycle) has diameter 5 and 6.

Written multiplicatively: `a = ofAdd 1`, `S = {1, a}`, and `sL[k] = a^k` for `k < 2`. Entry `k` of the
targets is `a^k`, and the certificate writes `a^k` as a product of at most two factors `s⁻¹ * t`. -/

namespace BipartiteDD.Haar.Cycle10

abbrev Z5 := Multiplicative (ZMod 5)

def aZ : Z5 := Multiplicative.ofAdd 1

/-- The connection set `{1, a}`, as a list of its elements. -/
def sLZ : List Z5 := [1, aZ]

def SZ : Finset Z5 := {1, aZ}

/-- `a^k` for `k = 0, …, 4`. -/
def tgtZ : List Z5 :=
  [Multiplicative.ofAdd 0, Multiplicative.ofAdd 1, Multiplicative.ofAdd 2,
    Multiplicative.ofAdd 3, Multiplicative.ofAdd 4]

/-- The numbering of `ℤ/5`: `a^k` has index `k`. -/
def idxZ (x : Z5) : ℕ := (Multiplicative.toAdd x).val

/-- Left certificate: `a^k = (sL[i]⁻¹ sL[j]) (sL[i']⁻¹ sL[j'])` with `sL[i]⁻¹ sL[j] = a^(j - i)`. -/
def certL : List (List (ℕ × ℕ)) :=
  [[(0, 0), (0, 0)], [(0, 1), (0, 0)], [(0, 1), (0, 1)], [(1, 0), (1, 0)], [(1, 0), (0, 0)]]

/-- Right certificate: the pairs of `certL` swapped, since `sL[j] * sL[i]⁻¹ = a^(j - i)`. -/
def certR : List (List (ℕ × ℕ)) := certL.map fun w => w.map Prod.swap

theorem checkL : leftCertOK sLZ tgtZ 2 certL = true := by decide +kernel

theorem checkR : rightCertOK sLZ tgtZ 2 certR = true := by decide +kernel

theorem checkE : evenCertOK sLZ tgtZ 2 (certL.map fun w => (0, w)) = true := by decide +kernel

theorem sL_mem : ∀ s ∈ sLZ, s ∈ SZ := by decide +kernel

theorem idx_lt : ∀ x : Z5, idxZ x < tgtZ.length := fun x => by
  have key : ∀ y : ZMod 5, y.val < 5 := by decide +kernel
  simpa [idxZ, tgtZ] using key (Multiplicative.toAdd x)

theorem tgt_val : ∀ x : Z5, tgtZ.getD (idxZ x) 1 = x := fun x => by
  have key : ∀ y : ZMod 5, tgtZ.getD (idxZ (Multiplicative.ofAdd y)) 1 = Multiplicative.ofAdd y := by
    decide +kernel
  simpa using key (Multiplicative.toAdd x)

theorem cover_odd : ∀ x : Z5, IsLeftWord SZ 2 x :=
  isLeftWord_of_cert checkL sL_mem idxZ idx_lt tgt_val

theorem cover_odd_right : ∀ x : Z5, IsRightWord SZ 2 x :=
  isRightWord_of_cert checkR sL_mem idxZ idx_lt tgt_val

theorem cover_even : ∀ x : Z5, ∃ s ∈ SZ, IsLeftWord SZ 2 (s⁻¹ * x) :=
  isEven_of_cert checkE sL_mem idxZ idx_lt tgt_val

/-- The 10-cycle has diameter at most 5. -/
theorem ediam_le_five : (haarGraph SZ).ediam ≤ 5 := by
  have h := haar_ediam_le_odd ⟨1, by decide +kernel⟩ 2 cover_odd cover_odd_right
  exact_mod_cast h

/-- The same graph has diameter at most 6, via the even statement with `s = 1`. -/
theorem ediam_le_six : (haarGraph SZ).ediam ≤ 6 := by
  have h := haar_ediam_le_even 2 cover_even
  exact_mod_cast h

end BipartiteDD.Haar.Cycle10
