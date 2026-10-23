import BipartiteDD.Haar.Main

/-! The diameter-8 lemma for Haar graphs (even `D`), from three covering hypotheses.

For `S ⊆ G`, the walk `(g, A) – (b₄ g, B) – (a₄⁻¹ b₄ g, A) – …` moves `A` to `A` in eight steps, and reaches
`(a₁⁻¹ b₁ ⋯ a₄⁻¹ b₄ g, A)`. The hypotheses are the words of length eight for `A`–`A` and `B`–`B`, and of
length seven for `A`–`B` (an `A`-to-`B` walk has odd length). Right multiplication is an automorphism, which is
not needed here: each pair of vertices is handled directly.

This is the even-`D` analogue of `ediam_le_five_of` in `BipartiteDD.Haar.Main`. It is a local statement for the
Δ7·D8 record; the general statement is meant to come from the `lemma` job (GraphD). -/

namespace BipartiteDD.Haar

open SimpleGraph

variable {G : Type*} [Group G]

theorem ediam_le_eight_of {W : Type*} (S : Finset G) (H : SimpleGraph W) (e : G ⊕ G ≃ W)
    (hH : ∀ x y, H.Adj (e x) (e y) ↔ (haarGraph S).Adj x y) (hS : S.Nonempty)
    (hAA : ∀ g : G, ∃ a1 ∈ S, ∃ b1 ∈ S, ∃ a2 ∈ S, ∃ b2 ∈ S, ∃ a3 ∈ S, ∃ b3 ∈ S, ∃ a4 ∈ S, ∃ b4 ∈ S,
      g = a1⁻¹ * b1 * (a2⁻¹ * b2) * (a3⁻¹ * b3) * (a4⁻¹ * b4))
    (hBB : ∀ g : G, ∃ a1 ∈ S, ∃ b1 ∈ S, ∃ a2 ∈ S, ∃ b2 ∈ S, ∃ a3 ∈ S, ∃ b3 ∈ S, ∃ a4 ∈ S, ∃ b4 ∈ S,
      g = a1 * b1⁻¹ * (a2 * b2⁻¹) * (a3 * b3⁻¹) * (a4 * b4⁻¹))
    (hAB : ∀ g : G, ∃ a ∈ S, ∃ a1 ∈ S, ∃ b1 ∈ S, ∃ a2 ∈ S, ∃ b2 ∈ S, ∃ a3 ∈ S, ∃ b3 ∈ S,
      g = a * (a1⁻¹ * b1) * (a2⁻¹ * b2) * (a3⁻¹ * b3)) :
    H.ediam ≤ 8 := by
  have adjA : ∀ g h s : G, s ∈ S → h = s * g → H.Adj (e (.inl g)) (e (.inr h)) := by
    intro g h s hs hh
    rw [hH, haarGraph_adj_inl_inr]
    subst hh
    rw [mul_inv_cancel_right]
    exact hs
  have adjB : ∀ g h s : G, s ∈ S → h = s * g → H.Adj (e (.inr h)) (e (.inl g)) :=
    fun g h s hs hh => (adjA g h s hs hh).symm
  -- `A` to `A`: `(g, A)` to `(W g, A)` with `W = a₁⁻¹ b₁ ⋯ a₄⁻¹ b₄`, eight steps
  have aa : ∀ g g' : G, H.edist (e (.inl g)) (e (.inl g')) ≤ 8 := by
    intro g g'
    obtain ⟨a1, ha1, b1, hb1, a2, ha2, b2, hb2, a3, ha3, b3, hb3, a4, ha4, b4, hb4, hx⟩ :=
      hAA (g' * g⁻¹)
    have hg : g' = a1⁻¹ * b1 * (a2⁻¹ * b2) * (a3⁻¹ * b3) * (a4⁻¹ * b4) * g := by
      rw [← hx]
      group
    subst hg
    exact (edist_le (Walk.cons (adjA g (b4 * g) b4 hb4 rfl)
      (Walk.cons (adjB (a4⁻¹ * b4 * g) (b4 * g) a4 ha4 (by group))
      (Walk.cons (adjA (a4⁻¹ * b4 * g) (b3 * (a4⁻¹ * b4 * g)) b3 hb3 rfl)
      (Walk.cons (adjB (a3⁻¹ * b3 * (a4⁻¹ * b4 * g)) (b3 * (a4⁻¹ * b4 * g)) a3 ha3 (by group))
      (Walk.cons (adjA (a3⁻¹ * b3 * (a4⁻¹ * b4 * g)) (b2 * (a3⁻¹ * b3 * (a4⁻¹ * b4 * g))) b2 hb2 rfl)
      (Walk.cons (adjB (a2⁻¹ * b2 * (a3⁻¹ * b3 * (a4⁻¹ * b4 * g)))
        (b2 * (a3⁻¹ * b3 * (a4⁻¹ * b4 * g))) a2 ha2 (by group))
      (Walk.cons (adjA (a2⁻¹ * b2 * (a3⁻¹ * b3 * (a4⁻¹ * b4 * g)))
        (b1 * (a2⁻¹ * b2 * (a3⁻¹ * b3 * (a4⁻¹ * b4 * g)))) b1 hb1 rfl)
      (Walk.cons (adjB (a1⁻¹ * b1 * (a2⁻¹ * b2) * (a3⁻¹ * b3) * (a4⁻¹ * b4) * g)
        (b1 * (a2⁻¹ * b2 * (a3⁻¹ * b3 * (a4⁻¹ * b4 * g)))) a1 ha1 (by group))
        Walk.nil))))))))).trans (by norm_num)
  -- `B` to `B`: `(h, B)` to `(W' h, B)` with `W' = a₁ b₁⁻¹ ⋯ a₄ b₄⁻¹`, eight steps
  have bb : ∀ h h' : G, H.edist (e (.inr h)) (e (.inr h')) ≤ 8 := by
    intro h h'
    obtain ⟨a1, ha1, b1, hb1, a2, ha2, b2, hb2, a3, ha3, b3, hb3, a4, ha4, b4, hb4, hx⟩ :=
      hBB (h' * h⁻¹)
    have hh : h' = a1 * b1⁻¹ * (a2 * b2⁻¹) * (a3 * b3⁻¹) * (a4 * b4⁻¹) * h := by
      rw [← hx]
      group
    subst hh
    exact (edist_le (Walk.cons (adjB (b4⁻¹ * h) h b4 hb4 (by group))
      (Walk.cons (adjA (b4⁻¹ * h) (a4 * (b4⁻¹ * h)) a4 ha4 rfl)
      (Walk.cons (adjB (b3⁻¹ * (a4 * (b4⁻¹ * h))) (a4 * (b4⁻¹ * h)) b3 hb3 (by group))
      (Walk.cons (adjA (b3⁻¹ * (a4 * (b4⁻¹ * h))) (a3 * (b3⁻¹ * (a4 * (b4⁻¹ * h)))) a3 ha3 rfl)
      (Walk.cons (adjB (b2⁻¹ * (a3 * (b3⁻¹ * (a4 * (b4⁻¹ * h)))))
        (a3 * (b3⁻¹ * (a4 * (b4⁻¹ * h)))) b2 hb2 (by group))
      (Walk.cons (adjA (b2⁻¹ * (a3 * (b3⁻¹ * (a4 * (b4⁻¹ * h)))))
        (a2 * (b2⁻¹ * (a3 * (b3⁻¹ * (a4 * (b4⁻¹ * h)))))) a2 ha2 rfl)
      (Walk.cons (adjB (b1⁻¹ * (a2 * (b2⁻¹ * (a3 * (b3⁻¹ * (a4 * (b4⁻¹ * h))))))) 
        (a2 * (b2⁻¹ * (a3 * (b3⁻¹ * (a4 * (b4⁻¹ * h)))))) b1 hb1 (by group))
      (Walk.cons (adjA (b1⁻¹ * (a2 * (b2⁻¹ * (a3 * (b3⁻¹ * (a4 * (b4⁻¹ * h))))))) 
        (a1 * b1⁻¹ * (a2 * b2⁻¹) * (a3 * b3⁻¹) * (a4 * b4⁻¹) * h) a1 ha1 (by group))
        Walk.nil))))))))).trans (by norm_num)
  -- `A` to `B`: `(g, A)` to `(x g, B)` with `x = a a₁⁻¹ b₁ a₂⁻¹ b₂ a₃⁻¹ b₃`, seven steps
  have ab : ∀ g h : G, H.edist (e (.inl g)) (e (.inr h)) ≤ 8 := by
    intro g h
    obtain ⟨a, ha, a1, ha1, b1, hb1, a2, ha2, b2, hb2, a3, ha3, b3, hb3, hx⟩ := hAB (h * g⁻¹)
    have hh : h = a * (a1⁻¹ * b1) * (a2⁻¹ * b2) * (a3⁻¹ * b3) * g := by
      rw [← hx]
      group
    subst hh
    exact (edist_le (Walk.cons (adjA g (b3 * g) b3 hb3 rfl)
      (Walk.cons (adjB (a3⁻¹ * b3 * g) (b3 * g) a3 ha3 (by group))
      (Walk.cons (adjA (a3⁻¹ * b3 * g) (b2 * (a3⁻¹ * b3 * g)) b2 hb2 rfl)
      (Walk.cons (adjB (a2⁻¹ * b2 * (a3⁻¹ * b3 * g)) (b2 * (a3⁻¹ * b3 * g)) a2 ha2 (by group))
      (Walk.cons (adjA (a2⁻¹ * b2 * (a3⁻¹ * b3 * g)) (b1 * (a2⁻¹ * b2 * (a3⁻¹ * b3 * g))) b1 hb1 rfl)
      (Walk.cons (adjB (a1⁻¹ * b1 * (a2⁻¹ * b2) * (a3⁻¹ * b3) * g)
        (b1 * (a2⁻¹ * b2 * (a3⁻¹ * b3 * g))) a1 ha1 (by group))
      (Walk.cons (adjA (a1⁻¹ * b1 * (a2⁻¹ * b2) * (a3⁻¹ * b3) * g)
        (a * (a1⁻¹ * b1) * (a2⁻¹ * b2) * (a3⁻¹ * b3) * g) a ha (by group))
        Walk.nil)))))))).trans (by norm_num)
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

/-- The Haar graph of `S`, transported along `e`, is bipartite of degree `|S|` and diameter `8`. -/
theorem isBipartiteDegDiam_eight_of {W : Type*} (S : Finset G) (H : SimpleGraph W) (e : G ⊕ G ≃ W)
    (hH : ∀ x y, H.Adj (e x) (e y) ↔ (haarGraph S).Adj x y) (hS : S.Nonempty)
    (hAA : ∀ g : G, ∃ a1 ∈ S, ∃ b1 ∈ S, ∃ a2 ∈ S, ∃ b2 ∈ S, ∃ a3 ∈ S, ∃ b3 ∈ S, ∃ a4 ∈ S, ∃ b4 ∈ S,
      g = a1⁻¹ * b1 * (a2⁻¹ * b2) * (a3⁻¹ * b3) * (a4⁻¹ * b4))
    (hBB : ∀ g : G, ∃ a1 ∈ S, ∃ b1 ∈ S, ∃ a2 ∈ S, ∃ b2 ∈ S, ∃ a3 ∈ S, ∃ b3 ∈ S, ∃ a4 ∈ S, ∃ b4 ∈ S,
      g = a1 * b1⁻¹ * (a2 * b2⁻¹) * (a3 * b3⁻¹) * (a4 * b4⁻¹))
    (hAB : ∀ g : G, ∃ a ∈ S, ∃ a1 ∈ S, ∃ b1 ∈ S, ∃ a2 ∈ S, ∃ b2 ∈ S, ∃ a3 ∈ S, ∃ b3 ∈ S,
      g = a * (a1⁻¹ * b1) * (a2⁻¹ * b2) * (a3⁻¹ * b3)) :
    IsBipartiteDegDiam H S.card 8 :=
  ⟨colorable_of S H e hH, degree_of S H e hH, ediam_le_eight_of S H e hH hS hAA hBB hAB⟩

/-- The same graph transported along any equivalence `e : G ⊕ G ≃ W`. -/
theorem isBipartiteDegDiam_eight_equiv {W : Type*} (S : Finset G) (e : G ⊕ G ≃ W) (hS : S.Nonempty)
    (hAA : ∀ g : G, ∃ a1 ∈ S, ∃ b1 ∈ S, ∃ a2 ∈ S, ∃ b2 ∈ S, ∃ a3 ∈ S, ∃ b3 ∈ S, ∃ a4 ∈ S, ∃ b4 ∈ S,
      g = a1⁻¹ * b1 * (a2⁻¹ * b2) * (a3⁻¹ * b3) * (a4⁻¹ * b4))
    (hBB : ∀ g : G, ∃ a1 ∈ S, ∃ b1 ∈ S, ∃ a2 ∈ S, ∃ b2 ∈ S, ∃ a3 ∈ S, ∃ b3 ∈ S, ∃ a4 ∈ S, ∃ b4 ∈ S,
      g = a1 * b1⁻¹ * (a2 * b2⁻¹) * (a3 * b3⁻¹) * (a4 * b4⁻¹))
    (hAB : ∀ g : G, ∃ a ∈ S, ∃ a1 ∈ S, ∃ b1 ∈ S, ∃ a2 ∈ S, ∃ b2 ∈ S, ∃ a3 ∈ S, ∃ b3 ∈ S,
      g = a * (a1⁻¹ * b1) * (a2⁻¹ * b2) * (a3⁻¹ * b3)) :
    IsBipartiteDegDiam ((haarGraph S).comap e.symm) S.card 8 :=
  isBipartiteDegDiam_eight_of S _ e (fun x y => by simp [SimpleGraph.comap_adj]) hS hAA hBB hAB

end BipartiteDD.Haar
