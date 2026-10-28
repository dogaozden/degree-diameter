import BipartiteDD.LeanMaxx.Haarconv.Ball
import BipartiteDD.Haar.Main

/-! The converse directions of the covering criterion for Haar graphs (`Theorem 2.4` of
`research/theorems/HAAR_D8_10.md`, the "only if" parts).

If the Haar graph of `S` has diameter at most a bound, then the covering hypotheses of the matching sufficiency
lemma hold: `haar_ediam_le_odd`, `haar_ediam_le_even` and `haar_ediam_le_five` (in `BipartiteDD.Haar`).

Proof idea. The distance from `(1, A)` to `(x, A)` is at most the diameter, so a walk of that length exists.
By `exists_lBall`, the vertex lies in the ball of some radius `k` no larger than the bound, and the ball
description gives the word. The same with `(1, B)` gives the right words. -/

namespace BipartiteDD.LeanMaxx.HaarConv

open SimpleGraph BipartiteDD.Haar

variable {G : Type*} [Group G]

/-- Converse of `haar_ediam_le_odd`: diameter at most `2 n + 1` gives both `n`-word covers. The hypothesis
`S.Nonempty` of `haar_ediam_le_odd` is not needed here, since an edgeless graph has infinite diameter. -/
theorem cover_of_ediam_le_odd {S : Finset G} (n : ℕ)
    (h : (haarGraph S).ediam ≤ ((2 * n + 1 : ℕ) : ENat)) :
    (∀ x : G, IsLeftWord S n x) ∧ (∀ x : G, IsRightWord S n x) := by
  constructor
  · intro x
    have hx : (haarGraph S).edist (.inl x) (.inl 1) ≤ ((2 * n + 1 : ℕ) : ENat) :=
      edist_le_ediam.trans h
    obtain ⟨k, hk, hball⟩ := exists_lBall hx
    rcases hball with ⟨j, hj, x', hx', hw⟩ | ⟨j, _, y, hy, _⟩
    · obtain rfl := Sum.inl.inj hx'
      exact isLeftWord_mono hw (by omega)
    · cases hy
  · intro x
    have hx : (haarGraph S).edist (.inr x) (.inr 1) ≤ ((2 * n + 1 : ℕ) : ENat) :=
      edist_le_ediam.trans h
    obtain ⟨k, hk, hball⟩ := exists_rBall hx
    rcases hball with ⟨j, hj, y, hy, hw⟩ | ⟨j, _, x', hx', _⟩
    · obtain rfl := Sum.inr.inj hy
      exact isRightWord_mono hw (by omega)
    · cases hx'

/-- Converse of `haar_ediam_le_even`: diameter at most `2 n + 2` gives the `n`-word cover of `s⁻¹ x`. -/
theorem cover_of_ediam_le_even {S : Finset G} (n : ℕ)
    (h : (haarGraph S).ediam ≤ ((2 * n + 2 : ℕ) : ENat)) :
    ∀ x : G, ∃ s ∈ S, IsLeftWord S n (s⁻¹ * x) := by
  intro x
  have hx : (haarGraph S).edist (.inr x) (.inl 1) ≤ ((2 * n + 2 : ℕ) : ENat) :=
    edist_le_ediam.trans h
  obtain ⟨k, hk, hball⟩ := exists_lBall hx
  rcases hball with ⟨j, _, x', hx', _⟩ | ⟨j, hj, y, hy, s, hs, hw⟩
  · cases hx'
  · obtain rfl := Sum.inr.inj hy
    exact ⟨s, hs, isLeftWord_mono hw (by omega)⟩

/-- A left word of at most two factors is a product `a⁻¹ b c⁻¹ d` with `a, b, c, d ∈ S`. Short words are padded
with a repeated factor `s⁻¹ s = 1`, which needs `S` nonempty. This is the four-factor form of `haar_ediam_le_five`. -/
theorem four_of_isLeftWord_two {S : Finset G} (hS : S.Nonempty) {g : G} (h : IsLeftWord S 2 g) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, g = a⁻¹ * b * c⁻¹ * d := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨w, hw, hmem, hp⟩ := h
  rcases w with _ | ⟨⟨p1, p2⟩, _ | ⟨⟨p3, p4⟩, _ | ⟨q, tail⟩⟩⟩
  · simp only [List.map_nil, List.prod_nil] at hp
    exact ⟨s, hs, s, hs, s, hs, s, hs, by rw [← hp]; group⟩
  · obtain ⟨h1, h2⟩ := hmem (p1, p2) (by simp)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hp
    exact ⟨p1, h1, p2, h2, s, hs, s, hs, by rw [← hp]; group⟩
  · obtain ⟨h1, h2⟩ := hmem (p1, p2) (by simp)
    obtain ⟨h3, h4⟩ := hmem (p3, p4) (by simp)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hp
    exact ⟨p1, h1, p2, h2, p3, h3, p4, h4, by rw [← hp]; group⟩
  · rw [List.length_cons, List.length_cons, List.length_cons] at hw
    omega

/-- The right-word analogue of `four_of_isLeftWord_two`. -/
theorem four_of_isRightWord_two {S : Finset G} (hS : S.Nonempty) {g : G} (h : IsRightWord S 2 g) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, g = a * b⁻¹ * c * d⁻¹ := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨w, hw, hmem, hp⟩ := h
  rcases w with _ | ⟨⟨p1, p2⟩, _ | ⟨⟨p3, p4⟩, _ | ⟨q, tail⟩⟩⟩
  · simp only [List.map_nil, List.prod_nil] at hp
    exact ⟨s, hs, s, hs, s, hs, s, hs, by rw [← hp]; group⟩
  · obtain ⟨h1, h2⟩ := hmem (p1, p2) (by simp)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hp
    exact ⟨p1, h1, p2, h2, s, hs, s, hs, by rw [← hp]; group⟩
  · obtain ⟨h1, h2⟩ := hmem (p1, p2) (by simp)
    obtain ⟨h3, h4⟩ := hmem (p3, p4) (by simp)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hp
    exact ⟨p1, h1, p2, h2, p3, h3, p4, h4, by rw [← hp]; group⟩
  · rw [List.length_cons, List.length_cons, List.length_cons] at hw
    omega

/-- Converse of `haar_ediam_le_five`: diameter at most `5` gives the two covering hypotheses of that lemma,
the four-factor forms `g = a⁻¹ b c⁻¹ d` and `g = a b⁻¹ c d⁻¹` with `a, b, c, d ∈ S`. -/
theorem cover_of_ediam_le_five (S : Finset G) (hS : S.Nonempty) (h : (haarGraph S).ediam ≤ 5) :
    (∀ g : G, ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, g = a⁻¹ * b * c⁻¹ * d) ∧
      (∀ g : G, ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, g = a * b⁻¹ * c * d⁻¹) := by
  have h5 : (haarGraph S).ediam ≤ ((2 * 2 + 1 : ℕ) : ENat) := by simpa using h
  obtain ⟨hL, hR⟩ := cover_of_ediam_le_odd 2 h5
  exact ⟨fun g => four_of_isLeftWord_two hS (hL g), fun g => four_of_isRightWord_two hS (hR g)⟩

/-- `haar_ediam_le_five` and its converse together: the diameter bound 5 is equivalent to the two covers. -/
theorem ediam_le_five_iff (S : Finset G) (hS : S.Nonempty) :
    (haarGraph S).ediam ≤ 5 ↔
      ((∀ g : G, ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, g = a⁻¹ * b * c⁻¹ * d) ∧
        (∀ g : G, ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, g = a * b⁻¹ * c * d⁻¹)) :=
  ⟨cover_of_ediam_le_five S hS, fun ⟨hA, hB⟩ => haar_ediam_le_five S hS hA hB⟩

end BipartiteDD.LeanMaxx.HaarConv
