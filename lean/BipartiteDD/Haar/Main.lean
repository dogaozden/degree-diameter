import BipartiteDD.Basic
import BipartiteDD.Haar.Graph
import BipartiteDD.Haar.GraphD
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Group

/-! The diameter-5 lemma for Haar graphs.

Let `S ⊆ G` be nonempty, with every `g` a product `a⁻¹ b c⁻¹ d` and also a product `a b⁻¹ c d⁻¹`
(`a, b, c, d ∈ S`). Then the Haar graph of `S` has diameter at most 5.

Proof. Walks from `(g, A)` go `(g, A) – (s g, B) – (c⁻¹ s g, A) – …`, so the `A`-vertices within
distance 4 of `(g, A)` are `(S⁻¹S)² g`, and the `B`-vertices within distance 4 of `(h, B)` are
`(SS⁻¹)² h`. Hypothesis `hA` covers all of `G` by the first, `hB` by the second. For `A` to `B`
at distance 5: step from `(g, A)` to `(s g, B)` for some `s ∈ S`, then `B` to `B` in 4 steps.

The statements are on an arbitrary graph `H` on `W`, transported from `G ⊕ G` along an equivalence
`e` (as in `Plus2.Graph`). This gives the graph on `G ⊕ G` itself (`e = Equiv.refl`) and its
transport to `Fin (2 * |G|)` with the same proof. -/

namespace BipartiteDD.Haar

open SimpleGraph

variable {G : Type*} [Group G]

/-- The Haar graph has degree at most `|S|`. -/
theorem haar_degree (S : Finset G) (x : G ⊕ G) :
    ((haarGraph S).neighborSet x).ncard ≤ S.card := by
  rcases x with g | g
  · have hsub : (haarGraph S).neighborSet (.inl g) ⊆
        (fun s => (Sum.inr (s * g) : G ⊕ G)) '' (S : Set G) := by
      intro y hy
      rw [mem_neighborSet] at hy
      rcases y with h | h
      · exact absurd hy (haarGraph_not_adj_inl_inl S g h)
      · rw [haarGraph_adj_inl_inr] at hy
        exact ⟨h * g⁻¹, hy, by simp⟩
    calc ((haarGraph S).neighborSet (.inl g)).ncard
        ≤ ((fun s => (Sum.inr (s * g) : G ⊕ G)) '' (S : Set G)).ncard :=
          Set.ncard_le_ncard hsub (S.finite_toSet.image _)
      _ ≤ (S : Set G).ncard := Set.ncard_image_le S.finite_toSet
      _ = S.card := Set.ncard_coe_finset S
  · have hsub : (haarGraph S).neighborSet (.inr g) ⊆
        (fun s => (Sum.inl (s⁻¹ * g) : G ⊕ G)) '' (S : Set G) := by
      intro y hy
      rw [mem_neighborSet] at hy
      rcases y with h | h
      · rw [haarGraph_adj_inr_inl] at hy
        exact ⟨g * h⁻¹, hy, by simp⟩
      · exact absurd hy (haarGraph_not_adj_inr_inr S g h)
    calc ((haarGraph S).neighborSet (.inr g)).ncard
        ≤ ((fun s => (Sum.inl (s⁻¹ * g) : G ⊕ G)) '' (S : Set G)).ncard :=
          Set.ncard_le_ncard hsub (S.finite_toSet.image _)
      _ ≤ (S : Set G).ncard := Set.ncard_image_le S.finite_toSet
      _ = S.card := Set.ncard_coe_finset S

/-- Colours: the `A` side is `0`, the `B` side is `1`. Adjacent vertices get different colours. -/
theorem color_ne (S : Finset G) {x y : G ⊕ G} (h : (haarGraph S).Adj x y) :
    Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1) x ≠
      Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1) y := by
  rcases x with g | g <;> rcases y with g' | g'
  · exact absurd h (haarGraph_not_adj_inl_inl S g g')
  · simp
  · simp
  · exact absurd h (haarGraph_not_adj_inr_inr S g g')

/-- A graph `H` on `W` that is the Haar graph of `S` along `e` is 2-colourable. -/
theorem colorable_of {W : Type*} (S : Finset G) (H : SimpleGraph W) (e : G ⊕ G ≃ W)
    (hH : ∀ x y, H.Adj (e x) (e y) ↔ (haarGraph S).Adj x y) : H.Colorable 2 := by
  refine ⟨Coloring.mk (fun w => Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1) (e.symm w)) ?_⟩
  intro u v huv
  have h : (haarGraph S).Adj (e.symm u) (e.symm v) := (hH _ _).1 (by simpa using huv)
  exact color_ne S h

/-- Degree bound on `W`: the neighbourhood of `e x` is the image of that of `x`. -/
theorem degree_of {W : Type*} (S : Finset G) (H : SimpleGraph W) (e : G ⊕ G ≃ W)
    (hH : ∀ x y, H.Adj (e x) (e y) ↔ (haarGraph S).Adj x y) (w : W) :
    (H.neighborSet w).ncard ≤ S.card := by
  obtain ⟨x, rfl⟩ := e.surjective w
  have hset : H.neighborSet (e x) = e '' (haarGraph S).neighborSet x := by
    ext w
    obtain ⟨y, rfl⟩ := e.surjective w
    simp only [mem_neighborSet, e.injective.mem_set_image, hH]
  rw [hset, Set.ncard_image_of_injective _ e.injective]
  exact haar_degree S x

/-- Diameter at most 5 on `W`, under the hypotheses on `G`. -/
theorem ediam_le_five_of {W : Type*} (S : Finset G) (H : SimpleGraph W) (e : G ⊕ G ≃ W)
    (hH : ∀ x y, H.Adj (e x) (e y) ↔ (haarGraph S).Adj x y) (hS : S.Nonempty)
    (hA : ∀ g : G, ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, g = a⁻¹ * b * c⁻¹ * d)
    (hB : ∀ g : G, ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, g = a * b⁻¹ * c * d⁻¹) :
    H.ediam ≤ 5 := by
  -- the two kinds of edge, read off from `hH`: `(g, A) ~ (s g, B)` for `s ∈ S`
  have adjA : ∀ g h s : G, s ∈ S → h = s * g → H.Adj (e (.inl g)) (e (.inr h)) := by
    intro g h s hs hh
    rw [hH, haarGraph_adj_inl_inr]
    subst hh
    rw [mul_inv_cancel_right]
    exact hs
  have adjB : ∀ g h s : G, s ∈ S → h = s * g → H.Adj (e (.inr h)) (e (.inl g)) :=
    fun g h s hs hh => (adjA g h s hs hh).symm
  -- `A` to `A` within 4 steps: `(g, A) – (d g, B) – (c⁻¹ d g, A) – (b c⁻¹ d g, B) – (a⁻¹ b c⁻¹ d g, A)`
  have aa : ∀ g g' : G, H.edist (e (.inl g)) (e (.inl g')) ≤ 4 := by
    intro g g'
    obtain ⟨a, ha, b, hb, c, hc, d, hd, hx⟩ := hA (g' * g⁻¹)
    have hg : g' = a⁻¹ * b * c⁻¹ * d * g := by
      rw [← hx]
      group
    subst hg
    exact (edist_le (Walk.cons (adjA g (d * g) d hd rfl)
      (Walk.cons (adjB (c⁻¹ * d * g) (d * g) c hc (by group))
      (Walk.cons (adjA (c⁻¹ * d * g) (b * c⁻¹ * d * g) b hb (by group))
      (Walk.cons (adjB (a⁻¹ * b * c⁻¹ * d * g) (b * c⁻¹ * d * g) a ha (by group))
        Walk.nil))))).trans (by norm_num)
  -- `B` to `B` within 4 steps: `(h, B) – (d⁻¹ h, A) – (c d⁻¹ h, B) – (b⁻¹ c d⁻¹ h, A) – (a b⁻¹ c d⁻¹ h, B)`
  have bb : ∀ h h' : G, H.edist (e (.inr h)) (e (.inr h')) ≤ 4 := by
    intro h h'
    obtain ⟨a, ha, b, hb, c, hc, d, hd, hx⟩ := hB (h' * h⁻¹)
    have hh : h' = a * b⁻¹ * c * d⁻¹ * h := by
      rw [← hx]
      group
    subst hh
    exact (edist_le (Walk.cons (adjB (d⁻¹ * h) h d hd (by group))
      (Walk.cons (adjA (d⁻¹ * h) (c * d⁻¹ * h) c hc (by group))
      (Walk.cons (adjB (b⁻¹ * c * d⁻¹ * h) (c * d⁻¹ * h) b hb (by group))
      (Walk.cons (adjA (b⁻¹ * c * d⁻¹ * h) (a * b⁻¹ * c * d⁻¹ * h) a ha (by group))
        Walk.nil))))).trans (by norm_num)
  -- `A` to `B` within 5 steps: one step to `(s g, B)`, then `B` to `B` within 4
  have ab : ∀ g h : G, H.edist (e (.inl g)) (e (.inr h)) ≤ 5 := by
    intro g h
    obtain ⟨s, hs⟩ := hS
    have h1 : H.edist (e (.inl g)) (e (.inr (s * g))) ≤ 1 :=
      (edist_le (Walk.cons (adjA g (s * g) s hs rfl) Walk.nil)).trans (by norm_num)
    calc H.edist (e (.inl g)) (e (.inr h))
        ≤ H.edist (e (.inl g)) (e (.inr (s * g))) + H.edist (e (.inr (s * g))) (e (.inr h)) :=
          SimpleGraph.edist_triangle
      _ ≤ 1 + 4 := add_le_add h1 (bb (s * g) h)
      _ = 5 := by norm_num
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

/-- The three properties, for a Haar graph transported along `e`. -/
theorem isBipartiteDegDiam_of {W : Type*} (S : Finset G) (H : SimpleGraph W) (e : G ⊕ G ≃ W)
    (hH : ∀ x y, H.Adj (e x) (e y) ↔ (haarGraph S).Adj x y) (hS : S.Nonempty)
    (hA : ∀ g : G, ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, g = a⁻¹ * b * c⁻¹ * d)
    (hB : ∀ g : G, ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, g = a * b⁻¹ * c * d⁻¹) :
    IsBipartiteDegDiam H S.card 5 :=
  ⟨colorable_of S H e hH, degree_of S H e hH, ediam_le_five_of S H e hH hS hA hB⟩

/-! The statements on `G ⊕ G` itself. -/

theorem haar_colorable (S : Finset G) : (haarGraph S).Colorable 2 :=
  colorable_of S (haarGraph S) (Equiv.refl _) (fun _ _ => Iff.rfl)

theorem haar_ediam_le_five (S : Finset G) (hS : S.Nonempty)
    (hA : ∀ g : G, ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, g = a⁻¹ * b * c⁻¹ * d)
    (hB : ∀ g : G, ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, g = a * b⁻¹ * c * d⁻¹) :
    (haarGraph S).ediam ≤ 5 := by
  -- the `n = 2` case of `haar_ediam_le_odd` (in `GraphD`)
  have h := haar_ediam_le_odd hS 2 (fun x => isLeftWord_two_of_four (hA x))
    (fun x => isRightWord_two_of_four (hB x))
  simpa using h

/-- The Haar graph of `S` on `G ⊕ G`, with `|S|` as degree bound and diameter 5. -/
theorem haar_isBipartiteDegDiam (S : Finset G) (hS : S.Nonempty)
    (hA : ∀ g : G, ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, g = a⁻¹ * b * c⁻¹ * d)
    (hB : ∀ g : G, ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, g = a * b⁻¹ * c * d⁻¹) :
    IsBipartiteDegDiam (haarGraph S) S.card 5 :=
  isBipartiteDegDiam_of S (haarGraph S) (Equiv.refl _) (fun _ _ => Iff.rfl) hS hA hB

/-- Odd diameter `2 n + 1` on `G ⊕ G`: degree `|S|`, bipartite, from `n`-word covers of both sides. -/
theorem haar_isBipartiteDegDiam_odd (S : Finset G) (hS : S.Nonempty) (n : ℕ)
    (hA : ∀ x : G, IsLeftWord S n x) (hB : ∀ x : G, IsRightWord S n x) :
    IsBipartiteDegDiam (haarGraph S) S.card (2 * n + 1) :=
  ⟨haar_colorable S, haar_degree S, haar_ediam_le_odd hS n hA hB⟩

/-- Even diameter `2 n + 2` on `G ⊕ G`: degree `|S|`, bipartite, from the even cover `S (S⁻¹S)^n = G`. -/
theorem haar_isBipartiteDegDiam_even (S : Finset G) (n : ℕ)
    (hA : ∀ x : G, ∃ s ∈ S, IsLeftWord S n (s⁻¹ * x)) :
    IsBipartiteDegDiam (haarGraph S) S.card (2 * n + 2) :=
  ⟨haar_colorable S, haar_degree S, haar_ediam_le_even n hA⟩

/-- The same graph transported along any equivalence `e : G ⊕ G ≃ W`. -/
theorem haar_isBipartiteDegDiam_of_equiv {W : Type*} (S : Finset G) (e : G ⊕ G ≃ W)
    (hS : S.Nonempty)
    (hA : ∀ g : G, ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, g = a⁻¹ * b * c⁻¹ * d)
    (hB : ∀ g : G, ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, g = a * b⁻¹ * c * d⁻¹) :
    IsBipartiteDegDiam ((haarGraph S).comap e.symm) S.card 5 :=
  isBipartiteDegDiam_of S _ e (fun x y => by simp [SimpleGraph.comap_adj]) hS hA hB

section Fin

variable [Fintype G]

/-- An equivalence `G ⊕ G ≃ Fin (2 * |G|)`. -/
noncomputable def haarEquiv : G ⊕ G ≃ Fin (2 * Fintype.card G) :=
  (Equiv.sumCongr (Fintype.equivFin G) (Fintype.equivFin G)).trans
    (finSumFinEquiv.trans (finCongr (two_mul _).symm))

/-- The Haar graph of `S`, as a graph on `Fin (2 * |G|)`. -/
theorem haar_isBipartiteDegDiam_fin (S : Finset G) (hS : S.Nonempty)
    (hA : ∀ g : G, ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, g = a⁻¹ * b * c⁻¹ * d)
    (hB : ∀ g : G, ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, g = a * b⁻¹ * c * d⁻¹) :
    ∃ H : SimpleGraph (Fin (2 * Fintype.card G)), IsBipartiteDegDiam H S.card 5 :=
  ⟨_, haar_isBipartiteDegDiam_of_equiv S haarEquiv hS hA hB⟩

end Fin

end BipartiteDD.Haar
