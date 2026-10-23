import BipartiteDD.Haar.Main

/-! The diameter-8 lemma for Haar graphs, the even case beside `Main` (diameter 5).

Let `S ⊆ G`. Suppose that every `x` is a product of eight letters of `S` in each of three patterns:
* (A) `x = p₁⁻¹ p₂ p₃⁻¹ p₄ p₅⁻¹ p₆ p₇⁻¹ p₈`,
* (B) `x = p₁ p₂⁻¹ p₃ p₄⁻¹ p₅ p₆⁻¹ p₇ p₈⁻¹`,
* (C) `x = p₁ p₂⁻¹ p₃ p₄⁻¹ p₅ p₆⁻¹ p₇` (seven letters),
with all `pᵢ ∈ S`. Then the Haar graph of `S` has diameter at most 8.

Walks: `(g, A) – (s g, B) – (t⁻¹ s g, A) – …`. A walk of length `2k` from `(g, A)` to `(x g, A)` exists when
`x` is a product of `k` factors `t⁻¹ s`, so (A) gives all `A`–`A` pairs within 8 steps. Likewise (B) gives all
`B`–`B` pairs within 8 steps. For `A`–`B`, one step to `(s g, B)` and then a `B`–`B` walk of length 6 reaches
`(x g, B)` when `x` is a product `p₁ p₂⁻¹ p₃ p₄⁻¹ p₅ p₆⁻¹` times `s`, which is (C) with seven letters. -/

namespace BipartiteDD.Haar

open SimpleGraph

variable {G : Type*} [Group G]

theorem ediam_le_eight_of {W : Type*} (S : Finset G) (H : SimpleGraph W) (e : G ⊕ G ≃ W)
    (hH : ∀ x y, H.Adj (e x) (e y) ↔ (haarGraph S).Adj x y)
    (hA : ∀ x : G, ∃ p₁ ∈ S, ∃ p₂ ∈ S, ∃ p₃ ∈ S, ∃ p₄ ∈ S, ∃ p₅ ∈ S, ∃ p₆ ∈ S, ∃ p₇ ∈ S, ∃ p₈ ∈ S,
      x = p₁⁻¹ * p₂ * p₃⁻¹ * p₄ * p₅⁻¹ * p₆ * p₇⁻¹ * p₈)
    (hB : ∀ x : G, ∃ p₁ ∈ S, ∃ p₂ ∈ S, ∃ p₃ ∈ S, ∃ p₄ ∈ S, ∃ p₅ ∈ S, ∃ p₆ ∈ S, ∃ p₇ ∈ S, ∃ p₈ ∈ S,
      x = p₁ * p₂⁻¹ * p₃ * p₄⁻¹ * p₅ * p₆⁻¹ * p₇ * p₈⁻¹)
    (hC : ∀ x : G, ∃ p₁ ∈ S, ∃ p₂ ∈ S, ∃ p₃ ∈ S, ∃ p₄ ∈ S, ∃ p₅ ∈ S, ∃ p₆ ∈ S, ∃ p₇ ∈ S,
      x = p₁ * p₂⁻¹ * p₃ * p₄⁻¹ * p₅ * p₆⁻¹ * p₇) :
    H.ediam ≤ 8 := by
  -- the two kinds of edge, read off from `hH`: `(g, A) ~ (s g, B)` for `s ∈ S`
  have adjA : ∀ g h s : G, s ∈ S → h = s * g → H.Adj (e (.inl g)) (e (.inr h)) := by
    intro g h s hs hh
    rw [hH, haarGraph_adj_inl_inr]
    subst hh
    rw [mul_inv_cancel_right]
    exact hs
  -- `(h, B) ~ (g, A)` when `h = s g`; the first argument is the `A`-vertex
  have adjB : ∀ g h s : G, s ∈ S → h = s * g → H.Adj (e (.inr h)) (e (.inl g)) :=
    fun g h s hs hh => (adjA g h s hs hh).symm
  -- `A` to `A` within 8 steps
  have aa : ∀ g g' : G, H.edist (e (.inl g)) (e (.inl g')) ≤ 8 := by
    intro g g'
    obtain ⟨p₁, h₁, p₂, h₂, p₃, h₃, p₄, h₄, p₅, h₅, p₆, h₆, p₇, h₇, p₈, h₈, hx⟩ := hA (g' * g⁻¹)
    have hg : g' = p₁⁻¹ * p₂ * p₃⁻¹ * p₄ * p₅⁻¹ * p₆ * p₇⁻¹ * p₈ * g := by
      rw [← hx]
      group
    subst hg
    exact (edist_le (Walk.cons (adjA g (p₈ * g) p₈ h₈ rfl)
      (Walk.cons (adjB (p₇⁻¹ * p₈ * g) (p₈ * g) p₇ h₇ (by group))
      (Walk.cons (adjA (p₇⁻¹ * p₈ * g) (p₆ * p₇⁻¹ * p₈ * g) p₆ h₆ (by group))
      (Walk.cons (adjB (p₅⁻¹ * p₆ * p₇⁻¹ * p₈ * g) (p₆ * p₇⁻¹ * p₈ * g) p₅ h₅ (by group))
      (Walk.cons (adjA (p₅⁻¹ * p₆ * p₇⁻¹ * p₈ * g) (p₄ * p₅⁻¹ * p₆ * p₇⁻¹ * p₈ * g) p₄ h₄ (by group))
      (Walk.cons (adjB (p₃⁻¹ * p₄ * p₅⁻¹ * p₆ * p₇⁻¹ * p₈ * g) (p₄ * p₅⁻¹ * p₆ * p₇⁻¹ * p₈ * g) p₃ h₃
        (by group))
      (Walk.cons (adjA (p₃⁻¹ * p₄ * p₅⁻¹ * p₆ * p₇⁻¹ * p₈ * g) (p₂ * p₃⁻¹ * p₄ * p₅⁻¹ * p₆ * p₇⁻¹ * p₈ * g)
        p₂ h₂ (by group))
      (Walk.cons (adjB (p₁⁻¹ * p₂ * p₃⁻¹ * p₄ * p₅⁻¹ * p₆ * p₇⁻¹ * p₈ * g)
        (p₂ * p₃⁻¹ * p₄ * p₅⁻¹ * p₆ * p₇⁻¹ * p₈ * g) p₁ h₁ (by group))
        Walk.nil))))))))).trans (by norm_num)
  -- `B` to `B` within 8 steps
  have bb : ∀ h h' : G, H.edist (e (.inr h)) (e (.inr h')) ≤ 8 := by
    intro h h'
    obtain ⟨p₁, h₁, p₂, h₂, p₃, h₃, p₄, h₄, p₅, h₅, p₆, h₆, p₇, h₇, p₈, h₈, hx⟩ := hB (h' * h⁻¹)
    have hh : h' = p₁ * p₂⁻¹ * p₃ * p₄⁻¹ * p₅ * p₆⁻¹ * p₇ * p₈⁻¹ * h := by
      rw [← hx]
      group
    subst hh
    exact (edist_le (Walk.cons (adjB (p₈⁻¹ * h) h p₈ h₈ (by group))
      (Walk.cons (adjA (p₈⁻¹ * h) (p₇ * p₈⁻¹ * h) p₇ h₇ (by group))
      (Walk.cons (adjB (p₆⁻¹ * p₇ * p₈⁻¹ * h) (p₇ * p₈⁻¹ * h) p₆ h₆ (by group))
      (Walk.cons (adjA (p₆⁻¹ * p₇ * p₈⁻¹ * h) (p₅ * p₆⁻¹ * p₇ * p₈⁻¹ * h) p₅ h₅ (by group))
      (Walk.cons (adjB (p₄⁻¹ * p₅ * p₆⁻¹ * p₇ * p₈⁻¹ * h) (p₅ * p₆⁻¹ * p₇ * p₈⁻¹ * h) p₄ h₄ (by group))
      (Walk.cons (adjA (p₄⁻¹ * p₅ * p₆⁻¹ * p₇ * p₈⁻¹ * h) (p₃ * p₄⁻¹ * p₅ * p₆⁻¹ * p₇ * p₈⁻¹ * h) p₃ h₃
        (by group))
      (Walk.cons (adjB (p₂⁻¹ * p₃ * p₄⁻¹ * p₅ * p₆⁻¹ * p₇ * p₈⁻¹ * h) (p₃ * p₄⁻¹ * p₅ * p₆⁻¹ * p₇ * p₈⁻¹ * h)
        p₂ h₂ (by group))
      (Walk.cons (adjA (p₂⁻¹ * p₃ * p₄⁻¹ * p₅ * p₆⁻¹ * p₇ * p₈⁻¹ * h) (p₁ * p₂⁻¹ * p₃ * p₄⁻¹ * p₅ * p₆⁻¹ * p₇ * p₈⁻¹ * h)
        p₁ h₁ (by group))
        Walk.nil))))))))).trans (by norm_num)
  -- `A` to `B` within 7 steps: one step to `(p₇ g, B)`, then `B` to `B` in 6 steps
  have ab : ∀ g h : G, H.edist (e (.inl g)) (e (.inr h)) ≤ 7 := by
    intro g h
    obtain ⟨p₁, h₁, p₂, h₂, p₃, h₃, p₄, h₄, p₅, h₅, p₆, h₆, p₇, h₇, hx⟩ := hC (h * g⁻¹)
    have hh : h = p₁ * p₂⁻¹ * p₃ * p₄⁻¹ * p₅ * p₆⁻¹ * p₇ * g := by
      rw [← hx]
      group
    subst hh
    exact (edist_le (Walk.cons (adjA g (p₇ * g) p₇ h₇ rfl)
      (Walk.cons (adjB (p₆⁻¹ * p₇ * g) (p₇ * g) p₆ h₆ (by group))
      (Walk.cons (adjA (p₆⁻¹ * p₇ * g) (p₅ * p₆⁻¹ * p₇ * g) p₅ h₅ (by group))
      (Walk.cons (adjB (p₄⁻¹ * p₅ * p₆⁻¹ * p₇ * g) (p₅ * p₆⁻¹ * p₇ * g) p₄ h₄ (by group))
      (Walk.cons (adjA (p₄⁻¹ * p₅ * p₆⁻¹ * p₇ * g) (p₃ * p₄⁻¹ * p₅ * p₆⁻¹ * p₇ * g) p₃ h₃ (by group))
      (Walk.cons (adjB (p₂⁻¹ * p₃ * p₄⁻¹ * p₅ * p₆⁻¹ * p₇ * g) (p₃ * p₄⁻¹ * p₅ * p₆⁻¹ * p₇ * g) p₂ h₂
        (by group))
      (Walk.cons (adjA (p₂⁻¹ * p₃ * p₄⁻¹ * p₅ * p₆⁻¹ * p₇ * g) (p₁ * p₂⁻¹ * p₃ * p₄⁻¹ * p₅ * p₆⁻¹ * p₇ * g)
        p₁ h₁ (by group))
        Walk.nil)))))))).trans (by norm_num)
  rw [ediam_le_iff]
  intro w₁ w₂
  obtain ⟨u, rfl⟩ := e.surjective w₁
  obtain ⟨v, rfl⟩ := e.surjective w₂
  rcases u with g | g <;> rcases v with g' | g'
  · exact aa g g'
  · exact (ab g g').trans (by norm_num)
  · rw [edist_comm]
    exact (ab g' g).trans (by norm_num)
  · exact bb g g'

/-- The three properties for a Haar graph transported along `e`, with diameter `8`. -/
theorem isBipartiteDegDiam_eight_of {W : Type*} (S : Finset G) (H : SimpleGraph W) (e : G ⊕ G ≃ W)
    (hH : ∀ x y, H.Adj (e x) (e y) ↔ (haarGraph S).Adj x y)
    (hA : ∀ x : G, ∃ p₁ ∈ S, ∃ p₂ ∈ S, ∃ p₃ ∈ S, ∃ p₄ ∈ S, ∃ p₅ ∈ S, ∃ p₆ ∈ S, ∃ p₇ ∈ S, ∃ p₈ ∈ S,
      x = p₁⁻¹ * p₂ * p₃⁻¹ * p₄ * p₅⁻¹ * p₆ * p₇⁻¹ * p₈)
    (hB : ∀ x : G, ∃ p₁ ∈ S, ∃ p₂ ∈ S, ∃ p₃ ∈ S, ∃ p₄ ∈ S, ∃ p₅ ∈ S, ∃ p₆ ∈ S, ∃ p₇ ∈ S, ∃ p₈ ∈ S,
      x = p₁ * p₂⁻¹ * p₃ * p₄⁻¹ * p₅ * p₆⁻¹ * p₇ * p₈⁻¹)
    (hC : ∀ x : G, ∃ p₁ ∈ S, ∃ p₂ ∈ S, ∃ p₃ ∈ S, ∃ p₄ ∈ S, ∃ p₅ ∈ S, ∃ p₆ ∈ S, ∃ p₇ ∈ S,
      x = p₁ * p₂⁻¹ * p₃ * p₄⁻¹ * p₅ * p₆⁻¹ * p₇) :
    IsBipartiteDegDiam H S.card 8 :=
  ⟨colorable_of S H e hH, degree_of S H e hH, ediam_le_eight_of S H e hH hA hB hC⟩

end BipartiteDD.Haar
