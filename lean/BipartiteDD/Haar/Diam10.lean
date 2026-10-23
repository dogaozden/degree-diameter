import BipartiteDD.Haar.Main

/-! The diameter-10 lemma for Haar graphs, from one nine-letter cover.

Let `S ⊆ G`, and suppose every `g` is a product `x₁ (x₂⁻¹ (x₃ (x₄⁻¹ (x₅ (x₆⁻¹ (x₇ (x₈⁻¹ x₉))))))))` with all
`xᵢ ∈ S`. Then the Haar graph of `S` has diameter at most 10.

Proof. From `(g, A)` the edge to `(x₉ g, B)` followed by four `B`-to-`B` pair steps reaches
`x₁ (x₂⁻¹ (⋯ (x₉ g)))` in nine edges. Since every `t` is such a product times `g`, every `(g, A)` is within 9
of every `(t, B)`. Two `A`-vertices are then within 10, through a neighbour of the second on the `B` side, and
two `B`-vertices likewise. This is the even-`D` argument with one covering condition. -/

namespace BipartiteDD.Haar

open SimpleGraph

variable {G : Type*} [Group G]

/-- The diameter-10 bound on `W`, under the nine-letter cover. -/
theorem ediam_le_ten_of {W : Type*} (S : Finset G) (H : SimpleGraph W) (e : G ⊕ G ≃ W)
    (hH : ∀ x y, H.Adj (e x) (e y) ↔ (haarGraph S).Adj x y)
    (hC : ∀ g : G, ∃ x₁ ∈ S, ∃ x₂ ∈ S, ∃ x₃ ∈ S, ∃ x₄ ∈ S, ∃ x₅ ∈ S, ∃ x₆ ∈ S, ∃ x₇ ∈ S, ∃ x₈ ∈ S,
      ∃ x₉ ∈ S, g = x₁ * (x₂⁻¹ * (x₃ * (x₄⁻¹ * (x₅ * (x₆⁻¹ * (x₇ * (x₈⁻¹ * x₉)))))))) :
    H.ediam ≤ 10 := by
  obtain ⟨s₀, hs₀, -⟩ := hC 1
  -- an edge `(g, A) – (s g, B)`
  have adjA : ∀ g s : G, s ∈ S → H.Adj (e (.inl g)) (e (.inr (s * g))) := by
    intro g s hs
    rw [hH, haarGraph_adj_inl_inr, mul_inv_cancel_right]
    exact hs
  -- an edge `(s g, B) – (g, A)`
  have adjB : ∀ g s : G, s ∈ S → H.Adj (e (.inr (s * g))) (e (.inl g)) := by
    intro g s hs
    rw [hH, haarGraph_adj_inr_inl, mul_inv_cancel_right]
    exact hs
  -- two steps `(y, B) – (t⁻¹ y, A) – (s t⁻¹ y, B)`
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
  -- `(g, A)` to `(t, B)` in nine edges
  have ab : ∀ g t : G, H.edist (e (.inl g)) (e (.inr t)) ≤ 9 := by
    intro g t
    obtain ⟨x₁, hx₁, x₂, hx₂, x₃, hx₃, x₄, hx₄, x₅, hx₅, x₆, hx₆, x₇, hx₇, x₈, hx₈, x₉, hx₉, hx⟩ :=
      hC (t * g⁻¹)
    have ht : t = (t * g⁻¹) * g := by group
    rw [hx] at ht
    have p0 : H.edist (e (.inl g)) (e (.inr (x₉ * g))) ≤ 1 :=
      (edist_le (Walk.cons (adjA g x₉ hx₉) Walk.nil)).trans (by norm_num)
    have c1 := stepB (x₉ * g) x₇ x₈ hx₇ hx₈
    have c2 := stepB (x₇ * (x₈⁻¹ * (x₉ * g))) x₅ x₆ hx₅ hx₆
    have c3 := stepB (x₅ * (x₆⁻¹ * (x₇ * (x₈⁻¹ * (x₉ * g))))) x₃ x₄ hx₃ hx₄
    have c4 := stepB (x₃ * (x₄⁻¹ * (x₅ * (x₆⁻¹ * (x₇ * (x₈⁻¹ * (x₉ * g))))))) x₁ x₂ hx₁ hx₂
    have key := chain _ _ _ _ _ p0 (chain _ _ _ _ _ c1 (chain _ _ _ _ _ c2 (chain _ _ _ _ _ c3 c4)))
    have hend : x₁ * (x₂⁻¹ * (x₃ * (x₄⁻¹ * (x₅ * (x₆⁻¹ * (x₇ * (x₈⁻¹ * (x₉ * g)))))))) = t := by
      rw [ht]
      simp only [mul_assoc]
    rw [hend] at key
    exact key.trans (by norm_num)
  -- `(g, A)` to `(g', A)` in ten edges: nine to a `B`-neighbour of `g'`, then one more
  have aa : ∀ g g' : G, H.edist (e (.inl g)) (e (.inl g')) ≤ 10 := by
    intro g g'
    have p1 : H.edist (e (.inr (s₀ * g'))) (e (.inl g')) ≤ 1 :=
      (edist_le (Walk.cons (adjB g' s₀ hs₀) Walk.nil)).trans (by norm_num)
    exact (chain _ _ _ _ _ (ab g (s₀ * g')) p1).trans (by norm_num)
  -- `(h, B)` to `(h', B)` in ten edges, through an `A`-neighbour of `h'`
  have bb : ∀ h h' : G, H.edist (e (.inr h)) (e (.inr h')) ≤ 10 := by
    intro h h'
    have p1 : H.edist (e (.inr h')) (e (.inl (s₀⁻¹ * h'))) ≤ 1 := by
      have hadj : H.Adj (e (.inr h')) (e (.inl (s₀⁻¹ * h'))) := by
        rw [hH, haarGraph_adj_inr_inl]
        have : h' * (s₀⁻¹ * h')⁻¹ = s₀ := by group
        rw [this]
        exact hs₀
      exact (edist_le (Walk.cons hadj Walk.nil)).trans (by norm_num)
    have p2 : H.edist (e (.inr h)) (e (.inl (s₀⁻¹ * h'))) ≤ 9 := by
      rw [edist_comm]
      exact ab (s₀⁻¹ * h') h
    rw [edist_comm] at p1
    exact (chain _ _ _ _ _ p2 p1).trans (by norm_num)
  rw [ediam_le_iff]
  intro w₁ w₂
  obtain ⟨u, rfl⟩ := e.surjective w₁
  obtain ⟨v, rfl⟩ := e.surjective w₂
  rcases u with g | g <;> rcases v with g' | g'
  · exact aa g g'
  · exact (ab g g').trans (by decide)
  · rw [edist_comm]
    exact (ab g' g).trans (by decide)
  · exact bb g g'

/-- The three properties of `IsBipartiteDegDiam` for a Haar graph transported along `e`, with `D = 10`. -/
theorem isBipartiteDegDiam10_of {W : Type*} (S : Finset G) (H : SimpleGraph W) (e : G ⊕ G ≃ W)
    (hH : ∀ x y, H.Adj (e x) (e y) ↔ (haarGraph S).Adj x y)
    (hC : ∀ g : G, ∃ x₁ ∈ S, ∃ x₂ ∈ S, ∃ x₃ ∈ S, ∃ x₄ ∈ S, ∃ x₅ ∈ S, ∃ x₆ ∈ S, ∃ x₇ ∈ S, ∃ x₈ ∈ S,
      ∃ x₉ ∈ S, g = x₁ * (x₂⁻¹ * (x₃ * (x₄⁻¹ * (x₅ * (x₆⁻¹ * (x₇ * (x₈⁻¹ * x₉)))))))) :
    IsBipartiteDegDiam H S.card 10 :=
  ⟨colorable_of S H e hH, degree_of S H e hH, ediam_le_ten_of S H e hH hC⟩

/-- The Haar graph of `S`, transported to `G ⊕ G ≃ W` (the graph on `W` is `(haarGraph S).comap e.symm`),
has degree `|S|` and diameter 10, under the nine-letter cover. -/
theorem haar_isBipartiteDegDiam10_of_equiv {W : Type*} (S : Finset G) (e : G ⊕ G ≃ W)
    (hC : ∀ g : G, ∃ x₁ ∈ S, ∃ x₂ ∈ S, ∃ x₃ ∈ S, ∃ x₄ ∈ S, ∃ x₅ ∈ S, ∃ x₆ ∈ S, ∃ x₇ ∈ S, ∃ x₈ ∈ S,
      ∃ x₉ ∈ S, g = x₁ * (x₂⁻¹ * (x₃ * (x₄⁻¹ * (x₅ * (x₆⁻¹ * (x₇ * (x₈⁻¹ * x₉)))))))) :
    IsBipartiteDegDiam ((haarGraph S).comap e.symm) S.card 10 :=
  isBipartiteDegDiam10_of S _ e (fun x y => by simp [SimpleGraph.comap_adj]) hC

end BipartiteDD.Haar
