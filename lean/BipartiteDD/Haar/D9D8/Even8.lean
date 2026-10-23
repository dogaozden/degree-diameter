import BipartiteDD.Haar.Main

/-! The diameter-8 bound for Haar graphs of even diameter, transported along an equivalence `e : G ⊕ G ≃ W`.

`haar_ediam_le_even` (in `GraphD`) with `n = 3` bounds the diameter of the Haar graph on `G ⊕ G` by `8`, from
the even cover: every `x` is `s * y` with `s ∈ S` and `y` a product of three pairs `p⁻¹ * q` with `p, q ∈ S`.
Here the graph is moved to `W` along `e`: a shortest walk of the Haar graph is mapped to a walk of `H`, of the
same length. -/

namespace BipartiteDD.Haar

open SimpleGraph

variable {G : Type*} [Group G]

/-- Diameter at most `8` on `W`, from the even cover of `S` by three pairs. -/
theorem ediam_le_eight_even_of {W : Type*} (S : Finset G) (H : SimpleGraph W) (e : G ⊕ G ≃ W)
    (hH : ∀ x y, H.Adj (e x) (e y) ↔ (haarGraph S).Adj x y)
    (hA : ∀ x : G, ∃ s ∈ S, IsLeftWord S 3 (s⁻¹ * x)) : H.ediam ≤ 8 := by
  have hG : (haarGraph S).ediam ≤ 8 := (haar_ediam_le_even 3 hA).trans (by norm_num)
  rw [ediam_le_iff] at hG ⊢
  intro w₁ w₂
  obtain ⟨u, rfl⟩ := e.surjective w₁
  obtain ⟨v, rfl⟩ := e.surjective w₂
  let f : haarGraph S →g H := { toFun := e, map_rel' := fun h => (hH _ _).2 h }
  obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top (ne_top_of_le_ne_top (by norm_num) (hG u v))
  calc H.edist (e u) (e v) ≤ ((p.map f).length : ℕ∞) := edist_le _
    _ = ((p.length : ℕ) : ℕ∞) := by rw [Walk.length_map]
    _ = (haarGraph S).edist u v := by rw [hp]
    _ ≤ 8 := hG u v

/-- The three properties of `IsBipartiteDegDiam` for a Haar graph transported along `e`, with `D = 8`. -/
theorem isBipartiteDegDiam8_even_of {W : Type*} (S : Finset G) (H : SimpleGraph W) (e : G ⊕ G ≃ W)
    (hH : ∀ x y, H.Adj (e x) (e y) ↔ (haarGraph S).Adj x y)
    (hA : ∀ x : G, ∃ s ∈ S, IsLeftWord S 3 (s⁻¹ * x)) : IsBipartiteDegDiam H S.card 8 :=
  ⟨colorable_of S H e hH, degree_of S H e hH, ediam_le_eight_even_of S H e hH hA⟩

end BipartiteDD.Haar
