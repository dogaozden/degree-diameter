import BipartiteDD.Haar.Main

/-! The diameter-8 lemma for Haar graphs (the even-`D` analogue of `Main.lean`).

Let `S ⊆ G` be finite, and let `H` be the Haar graph of `S` transported along `e : G ⊕ G ≃ W`. Suppose:
* `hA`: every `g` is `a₁⁻¹ b₁ (a₂⁻¹ b₂) (a₃⁻¹ b₃) (a₄⁻¹ b₄)` with all letters in `S`;
* `hB`: every `g` is `a₁ b₁⁻¹ (a₂ b₂⁻¹) (a₃ b₃⁻¹) (a₄ b₄⁻¹)`;
* `hAB`: every `x` is `a₁ b₁⁻¹ (a₂ b₂⁻¹) (a₃ b₃⁻¹) s` with `s ∈ S`.

Then `H` has diameter at most 8, so the three properties of `IsBipartiteDegDiam` hold with `d = |S|`.

Walks: `(g, A) – (d g, B) – (c⁻¹ d g, A)` is a two-step walk, so `A`-vertices reach `c⁻¹ d g` in two steps;
`(h, B) – (d⁻¹ h, A) – (c d⁻¹ h, B)` is a two-step walk on the `B` side; and `(g, A) – (s g, B)` is one step.
The pair `(A, A)` uses four two-step walks (8 steps), `(B, B)` the same, `(A, B)` one step and three
`B`-`B` walks (7 steps). The argument is the one of `Main.lean` with longer words. -/

namespace BipartiteDD.Haar

open SimpleGraph

variable {G : Type*} [Group G]

theorem diam8_of {W : Type*} (S : Finset G) (H : SimpleGraph W) (e : G ⊕ G ≃ W)
    (hH : ∀ x y, H.Adj (e x) (e y) ↔ (haarGraph S).Adj x y)
    (hA : ∀ g : G, ∃ a₁ ∈ S, ∃ b₁ ∈ S, ∃ a₂ ∈ S, ∃ b₂ ∈ S, ∃ a₃ ∈ S, ∃ b₃ ∈ S, ∃ a₄ ∈ S, ∃ b₄ ∈ S,
      g = a₁⁻¹ * b₁ * (a₂⁻¹ * b₂) * (a₃⁻¹ * b₃) * (a₄⁻¹ * b₄))
    (hB : ∀ g : G, ∃ a₁ ∈ S, ∃ b₁ ∈ S, ∃ a₂ ∈ S, ∃ b₂ ∈ S, ∃ a₃ ∈ S, ∃ b₃ ∈ S, ∃ a₄ ∈ S, ∃ b₄ ∈ S,
      g = a₁ * b₁⁻¹ * (a₂ * b₂⁻¹) * (a₃ * b₃⁻¹) * (a₄ * b₄⁻¹))
    (hAB : ∀ x : G, ∃ s ∈ S, ∃ a₁ ∈ S, ∃ b₁ ∈ S, ∃ a₂ ∈ S, ∃ b₂ ∈ S, ∃ a₃ ∈ S, ∃ b₃ ∈ S,
      x = a₁ * b₁⁻¹ * (a₂ * b₂⁻¹) * (a₃ * b₃⁻¹) * s) :
    H.ediam ≤ 8 := by
  -- an edge of `H` from `(g, A)` to `(s g, B)`
  have adjA : ∀ g s : G, s ∈ S → H.Adj (e (.inl g)) (e (.inr (s * g))) := by
    intro g s hs
    rw [hH, haarGraph_adj_inl_inr, mul_inv_cancel_right]
    exact hs
  -- two steps `(g, A) – (d g, B) – (c⁻¹ d g, A)`
  have stepA : ∀ g c d : G, c ∈ S → d ∈ S →
      H.edist (e (.inl g)) (e (.inl (c⁻¹ * d * g))) ≤ 2 := by
    intro g c d hc hd
    have h2 : H.Adj (e (.inr (d * g))) (e (.inl (c⁻¹ * d * g))) := by
      rw [hH, haarGraph_adj_inr_inl]
      have : d * g * (c⁻¹ * d * g)⁻¹ = c := by group
      rw [this]
      exact hc
    exact (edist_le (Walk.cons (adjA g d hd) (Walk.cons h2 Walk.nil))).trans (by norm_num)
  -- two steps `(h, B) – (d⁻¹ h, A) – (c d⁻¹ h, B)`
  have stepB : ∀ h c d : G, c ∈ S → d ∈ S →
      H.edist (e (.inr h)) (e (.inr (c * d⁻¹ * h))) ≤ 2 := by
    intro h c d hc hd
    have h1 : H.Adj (e (.inr h)) (e (.inl (d⁻¹ * h))) := by
      rw [hH, haarGraph_adj_inr_inl]
      have : h * (d⁻¹ * h)⁻¹ = d := by group
      rw [this]
      exact hd
    have h2 : H.Adj (e (.inl (d⁻¹ * h))) (e (.inr (c * d⁻¹ * h))) := by
      rw [hH, haarGraph_adj_inl_inr]
      have : c * d⁻¹ * h * (d⁻¹ * h)⁻¹ = c := by group
      rw [this]
      exact hc
    exact (edist_le (Walk.cons h1 (Walk.cons h2 Walk.nil))).trans (by norm_num)
  -- distances add along a path
  have comp : ∀ {u v w : W} {m k : ℕ∞}, H.edist u v ≤ m → H.edist v w ≤ k → H.edist u w ≤ m + k :=
    fun h1 h2 => (SimpleGraph.edist_triangle).trans (add_le_add h1 h2)
  -- `(A, A)`: eight steps
  have aa : ∀ g g' : G, H.edist (e (.inl g)) (e (.inl g')) ≤ 8 := by
    intro g g'
    obtain ⟨a₁, ha₁, b₁, hb₁, a₂, ha₂, b₂, hb₂, a₃, ha₃, b₃, hb₃, a₄, ha₄, b₄, hb₄, hx⟩ :=
      hA (g' * g⁻¹)
    have hg : g' = a₁⁻¹ * b₁ * (a₂⁻¹ * b₂) * (a₃⁻¹ * b₃) * (a₄⁻¹ * b₄) * g := by
      rw [← hx, inv_mul_cancel_right]
    rw [hg]
    have hX : a₁⁻¹ * b₁ * (a₂⁻¹ * b₂) * (a₃⁻¹ * b₃) * (a₄⁻¹ * b₄) * g =
        a₁⁻¹ * b₁ * (a₂⁻¹ * b₂ * (a₃⁻¹ * b₃ * (a₄⁻¹ * b₄ * g))) := by
      simp only [mul_assoc]
    rw [hX]
    exact (comp (comp (comp (stepA g a₄ b₄ ha₄ hb₄) (stepA _ a₃ b₃ ha₃ hb₃))
      (stepA _ a₂ b₂ ha₂ hb₂)) (stepA _ a₁ b₁ ha₁ hb₁)).trans (by norm_num)
  -- `(B, B)`: eight steps
  have bb : ∀ h h' : G, H.edist (e (.inr h)) (e (.inr h')) ≤ 8 := by
    intro h h'
    obtain ⟨a₁, ha₁, b₁, hb₁, a₂, ha₂, b₂, hb₂, a₃, ha₃, b₃, hb₃, a₄, ha₄, b₄, hb₄, hx⟩ :=
      hB (h' * h⁻¹)
    have hh : h' = a₁ * b₁⁻¹ * (a₂ * b₂⁻¹) * (a₃ * b₃⁻¹) * (a₄ * b₄⁻¹) * h := by
      rw [← hx, inv_mul_cancel_right]
    rw [hh]
    have hX : a₁ * b₁⁻¹ * (a₂ * b₂⁻¹) * (a₃ * b₃⁻¹) * (a₄ * b₄⁻¹) * h =
        a₁ * b₁⁻¹ * (a₂ * b₂⁻¹ * (a₃ * b₃⁻¹ * (a₄ * b₄⁻¹ * h))) := by
      simp only [mul_assoc]
    rw [hX]
    exact (comp (comp (comp (stepB h a₄ b₄ ha₄ hb₄) (stepB _ a₃ b₃ ha₃ hb₃))
      (stepB _ a₂ b₂ ha₂ hb₂)) (stepB _ a₁ b₁ ha₁ hb₁)).trans (by norm_num)
  -- `(A, B)`: one step to `(s g, B)`, then three `B`-`B` walks (7 steps)
  have ab : ∀ g h : G, H.edist (e (.inl g)) (e (.inr h)) ≤ 8 := by
    intro g h
    obtain ⟨s, hs, a₁, ha₁, b₁, hb₁, a₂, ha₂, b₂, hb₂, a₃, ha₃, b₃, hb₃, hx⟩ := hAB (h * g⁻¹)
    have hh : h = a₁ * b₁⁻¹ * (a₂ * b₂⁻¹) * (a₃ * b₃⁻¹) * s * g := by
      rw [← hx, inv_mul_cancel_right]
    rw [hh]
    have hX : a₁ * b₁⁻¹ * (a₂ * b₂⁻¹) * (a₃ * b₃⁻¹) * s * g =
        a₁ * b₁⁻¹ * (a₂ * b₂⁻¹ * (a₃ * b₃⁻¹ * (s * g))) := by
      simp only [mul_assoc]
    rw [hX]
    have p0 : H.edist (e (.inl g)) (e (.inr (s * g))) ≤ 1 :=
      (edist_le (Walk.cons (adjA g s hs) Walk.nil)).trans (by norm_num)
    exact (comp (comp (comp p0 (stepB _ a₃ b₃ ha₃ hb₃)) (stepB _ a₂ b₂ ha₂ hb₂))
      (stepB _ a₁ b₁ ha₁ hb₁)).trans (by decide)
  rw [ediam_le_iff]
  intro w₁ w₂
  obtain ⟨u, rfl⟩ := e.surjective w₁
  obtain ⟨v, rfl⟩ := e.surjective w₂
  rcases u with g | g <;> rcases v with g' | g'
  · exact aa g g'
  · exact ab g g'
  · rw [edist_comm]
    exact ab g' g
  · exact bb g g'

/-- The three properties of `IsBipartiteDegDiam` for a Haar graph transported along `e`, with `D = 8`. -/
theorem isBipartiteDegDiam8_of {W : Type*} (S : Finset G) (H : SimpleGraph W) (e : G ⊕ G ≃ W)
    (hH : ∀ x y, H.Adj (e x) (e y) ↔ (haarGraph S).Adj x y)
    (hA : ∀ g : G, ∃ a₁ ∈ S, ∃ b₁ ∈ S, ∃ a₂ ∈ S, ∃ b₂ ∈ S, ∃ a₃ ∈ S, ∃ b₃ ∈ S, ∃ a₄ ∈ S, ∃ b₄ ∈ S,
      g = a₁⁻¹ * b₁ * (a₂⁻¹ * b₂) * (a₃⁻¹ * b₃) * (a₄⁻¹ * b₄))
    (hB : ∀ g : G, ∃ a₁ ∈ S, ∃ b₁ ∈ S, ∃ a₂ ∈ S, ∃ b₂ ∈ S, ∃ a₃ ∈ S, ∃ b₃ ∈ S, ∃ a₄ ∈ S, ∃ b₄ ∈ S,
      g = a₁ * b₁⁻¹ * (a₂ * b₂⁻¹) * (a₃ * b₃⁻¹) * (a₄ * b₄⁻¹))
    (hAB : ∀ x : G, ∃ s ∈ S, ∃ a₁ ∈ S, ∃ b₁ ∈ S, ∃ a₂ ∈ S, ∃ b₂ ∈ S, ∃ a₃ ∈ S, ∃ b₃ ∈ S,
      x = a₁ * b₁⁻¹ * (a₂ * b₂⁻¹) * (a₃ * b₃⁻¹) * s) :
    IsBipartiteDegDiam H S.card 8 :=
  ⟨colorable_of S H e hH, degree_of S H e hH, diam8_of S H e hH hA hB hAB⟩

end BipartiteDD.Haar
