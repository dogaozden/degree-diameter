import BipartiteDD.Haar.Main

/-! The diameter-9 lemma for Haar graphs, with four-pair covers.

Let `S ⊆ G` be nonempty, with every `g` a product `x1⁻¹ x2 x3⁻¹ x4 x5⁻¹ x6 x7⁻¹ x8` and also a product
`x1 x2⁻¹ x3 x4⁻¹ x5 x6⁻¹ x7 x8⁻¹` (all `xi ∈ S`). Then the Haar graph of `S` has diameter at most 9.

Proof. A pair step on the `A` side, `(y, A) – (s y, B) – (t⁻¹ s y, A)`, moves `y` to `t⁻¹ s y` in two
edges. Four pair steps reach `x1⁻¹ x2 x3⁻¹ x4 x5⁻¹ x6 x7⁻¹ x8 g` from `(g, A)` in eight edges, and the `B`
side is symmetric. An `A`-to-`B` pair is one edge plus eight.

This mirrors `Main.lean`, where the diameter-5 lemma uses two pair steps. The statements are on an arbitrary
graph `H` on `W`, transported from `G ⊕ G` along `e`, as there. -/

namespace BipartiteDD.Haar

open SimpleGraph

variable {G : Type*} [Group G]

/-- The diameter-9 bound on `W`, under the eight-letter covers. -/
theorem ediam_le_nine_of {W : Type*} (S : Finset G) (H : SimpleGraph W) (e : G ⊕ G ≃ W)
    (hH : ∀ x y, H.Adj (e x) (e y) ↔ (haarGraph S).Adj x y) (hS : S.Nonempty)
    (hA : ∀ g : G, ∃ x1 ∈ S, ∃ x2 ∈ S, ∃ x3 ∈ S, ∃ x4 ∈ S, ∃ x5 ∈ S, ∃ x6 ∈ S, ∃ x7 ∈ S, ∃ x8 ∈ S,
      g = x1⁻¹ * x2 * x3⁻¹ * x4 * x5⁻¹ * x6 * x7⁻¹ * x8)
    (hB : ∀ g : G, ∃ x1 ∈ S, ∃ x2 ∈ S, ∃ x3 ∈ S, ∃ x4 ∈ S, ∃ x5 ∈ S, ∃ x6 ∈ S, ∃ x7 ∈ S, ∃ x8 ∈ S,
      g = x1 * x2⁻¹ * x3 * x4⁻¹ * x5 * x6⁻¹ * x7 * x8⁻¹) :
    H.ediam ≤ 9 := by
  -- one `A`-to-`A` pair step: `y ↦ t⁻¹ s y` in two edges
  have stepA : ∀ y s t : G, s ∈ S → t ∈ S → H.edist (e (.inl y)) (e (.inl (t⁻¹ * s * y))) ≤ 2 := by
    intro y s t hs ht
    have h1 : H.Adj (e (.inl y)) (e (.inr (s * y))) := by
      rw [hH, haarGraph_adj_inl_inr, mul_inv_cancel_right]
      exact hs
    have h2 : H.Adj (e (.inr (s * y))) (e (.inl (t⁻¹ * s * y))) := by
      rw [hH, haarGraph_adj_inr_inl]
      have : s * y * (t⁻¹ * s * y)⁻¹ = t := by group
      rw [this]
      exact ht
    exact (edist_le (Walk.cons h1 (Walk.cons h2 Walk.nil))).trans (by norm_num)
  -- one `B`-to-`B` pair step: `y ↦ s t⁻¹ y` in two edges
  have stepB : ∀ y s t : G, s ∈ S → t ∈ S → H.edist (e (.inr y)) (e (.inr (s * (t⁻¹ * y)))) ≤ 2 := by
    intro y s t hs ht
    have h1 : H.Adj (e (.inr y)) (e (.inl (t⁻¹ * y))) := by
      rw [hH, haarGraph_adj_inr_inl]
      have : y * (t⁻¹ * y)⁻¹ = t := by group
      rw [this]
      exact ht
    have h2 : H.Adj (e (.inl (t⁻¹ * y))) (e (.inr (s * (t⁻¹ * y)))) := by
      rw [hH, haarGraph_adj_inl_inr, mul_inv_cancel_right]
      exact hs
    exact (edist_le (Walk.cons h1 (Walk.cons h2 Walk.nil))).trans (by norm_num)
  have chain : ∀ (u v w : W) (a b : ℕ∞), H.edist u v ≤ a → H.edist v w ≤ b → H.edist u w ≤ a + b :=
    fun u v w a b h1 h2 => SimpleGraph.edist_triangle.trans (add_le_add h1 h2)
  -- `A` to `A` within 8 steps
  have aa : ∀ g g' : G, H.edist (e (.inl g)) (e (.inl g')) ≤ 8 := by
    intro g g'
    obtain ⟨x1, hx1, x2, hx2, x3, hx3, x4, hx4, x5, hx5, x6, hx6, x7, hx7, x8, hx8, hx⟩ :=
      hA (g' * g⁻¹)
    have hg : g' = x1⁻¹ * x2 * x3⁻¹ * x4 * x5⁻¹ * x6 * x7⁻¹ * x8 * g := by
      rw [← hx]
      group
    subst hg
    have e1 := stepA g x8 x7 hx8 hx7
    have e2 := stepA (x7⁻¹ * x8 * g) x6 x5 hx6 hx5
    have e3 := stepA (x5⁻¹ * x6 * (x7⁻¹ * x8 * g)) x4 x3 hx4 hx3
    have e4 := stepA (x3⁻¹ * x4 * (x5⁻¹ * x6 * (x7⁻¹ * x8 * g))) x2 x1 hx2 hx1
    have hF : x1⁻¹ * x2 * x3⁻¹ * x4 * x5⁻¹ * x6 * x7⁻¹ * x8 * g
        = x1⁻¹ * x2 * (x3⁻¹ * x4 * (x5⁻¹ * x6 * (x7⁻¹ * x8 * g))) := by
      simp only [mul_assoc]
    rw [hF]
    exact (chain _ _ _ _ _ (chain _ _ _ _ _ (chain _ _ _ _ _ e1 e2) e3) e4).trans (by norm_num)
  -- `B` to `B` within 8 steps
  have bb : ∀ h h' : G, H.edist (e (.inr h)) (e (.inr h')) ≤ 8 := by
    intro h h'
    obtain ⟨x1, hx1, x2, hx2, x3, hx3, x4, hx4, x5, hx5, x6, hx6, x7, hx7, x8, hx8, hx⟩ :=
      hB (h' * h⁻¹)
    have hh : h' = x1 * x2⁻¹ * x3 * x4⁻¹ * x5 * x6⁻¹ * x7 * x8⁻¹ * h := by
      rw [← hx]
      group
    subst hh
    have e1 := stepB h x7 x8 hx7 hx8
    have e2 := stepB (x7 * (x8⁻¹ * h)) x5 x6 hx5 hx6
    have e3 := stepB (x5 * (x6⁻¹ * (x7 * (x8⁻¹ * h)))) x3 x4 hx3 hx4
    have e4 := stepB (x3 * (x4⁻¹ * (x5 * (x6⁻¹ * (x7 * (x8⁻¹ * h)))))) x1 x2 hx1 hx2
    have hF : x1 * x2⁻¹ * x3 * x4⁻¹ * x5 * x6⁻¹ * x7 * x8⁻¹ * h
        = x1 * (x2⁻¹ * (x3 * (x4⁻¹ * (x5 * (x6⁻¹ * (x7 * (x8⁻¹ * h))))))) := by
      simp only [mul_assoc]
    rw [hF]
    exact (chain _ _ _ _ _ (chain _ _ _ _ _ (chain _ _ _ _ _ e1 e2) e3) e4).trans (by norm_num)
  -- `A` to `B` within 9 steps: one step to `(s g, B)`, then `B` to `B` within 8
  have ab : ∀ g h : G, H.edist (e (.inl g)) (e (.inr h)) ≤ 9 := by
    intro g h
    obtain ⟨s, hs⟩ := hS
    have h1 : H.edist (e (.inl g)) (e (.inr (s * g))) ≤ 1 := by
      have hadj : H.Adj (e (.inl g)) (e (.inr (s * g))) := by
        rw [hH, haarGraph_adj_inl_inr, mul_inv_cancel_right]
        exact hs
      exact (edist_le (Walk.cons hadj Walk.nil)).trans (by norm_num)
    exact (chain _ _ _ _ _ h1 (bb (s * g) h)).trans (by norm_num)
  rw [ediam_le_iff]
  intro w₁ w₂
  obtain ⟨u, rfl⟩ := e.surjective w₁
  obtain ⟨v, rfl⟩ := e.surjective w₂
  rcases u with g | g <;> rcases v with g' | g'
  · exact (aa g g').trans (by decide)
  · exact ab g g'
  · rw [edist_comm]
    exact ab g' g
  · exact (bb g g').trans (by decide)

/-- The Haar graph of `S`, transported along any `e : G ⊕ G ≃ W`, has degree `|S|` and diameter 9. -/
theorem isBipartiteDegDiam9_of {W : Type*} (S : Finset G) (H : SimpleGraph W) (e : G ⊕ G ≃ W)
    (hH : ∀ x y, H.Adj (e x) (e y) ↔ (haarGraph S).Adj x y) (hS : S.Nonempty)
    (hA : ∀ g : G, ∃ x1 ∈ S, ∃ x2 ∈ S, ∃ x3 ∈ S, ∃ x4 ∈ S, ∃ x5 ∈ S, ∃ x6 ∈ S, ∃ x7 ∈ S, ∃ x8 ∈ S,
      g = x1⁻¹ * x2 * x3⁻¹ * x4 * x5⁻¹ * x6 * x7⁻¹ * x8)
    (hB : ∀ g : G, ∃ x1 ∈ S, ∃ x2 ∈ S, ∃ x3 ∈ S, ∃ x4 ∈ S, ∃ x5 ∈ S, ∃ x6 ∈ S, ∃ x7 ∈ S, ∃ x8 ∈ S,
      g = x1 * x2⁻¹ * x3 * x4⁻¹ * x5 * x6⁻¹ * x7 * x8⁻¹) :
    IsBipartiteDegDiam H S.card 9 :=
  ⟨colorable_of S H e hH, degree_of S H e hH, ediam_le_nine_of S H e hH hS hA hB⟩

/-- The same graph transported along any equivalence `e : G ⊕ G ≃ W`, as in `Main`. -/
theorem haar_isBipartiteDegDiam9_of_equiv {W : Type*} (S : Finset G) (e : G ⊕ G ≃ W)
    (hS : S.Nonempty)
    (hA : ∀ g : G, ∃ x1 ∈ S, ∃ x2 ∈ S, ∃ x3 ∈ S, ∃ x4 ∈ S, ∃ x5 ∈ S, ∃ x6 ∈ S, ∃ x7 ∈ S, ∃ x8 ∈ S,
      g = x1⁻¹ * x2 * x3⁻¹ * x4 * x5⁻¹ * x6 * x7⁻¹ * x8)
    (hB : ∀ g : G, ∃ x1 ∈ S, ∃ x2 ∈ S, ∃ x3 ∈ S, ∃ x4 ∈ S, ∃ x5 ∈ S, ∃ x6 ∈ S, ∃ x7 ∈ S, ∃ x8 ∈ S,
      g = x1 * x2⁻¹ * x3 * x4⁻¹ * x5 * x6⁻¹ * x7 * x8⁻¹) :
    IsBipartiteDegDiam ((haarGraph S).comap e.symm) S.card 9 :=
  isBipartiteDegDiam9_of S _ e (fun x y => by simp [SimpleGraph.comap_adj]) hS hA hB

end BipartiteDD.Haar
