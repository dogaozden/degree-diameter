import BipartiteDD.LeanMaxx.D5.Degree
import BipartiteDD.GQ4.Count
import BipartiteDD.GQST.Main

/-! # D = 5 formalisation, part 6: Theorem 3.5 with its order

`research/theorems/D5_QUADRANGLE.md` Theorem 3.5/3.6: if every arc satisfies (T') (in particular if it is repaired)
and same-colour hubs are within distance `4`, and the hub graph has maximum degree `≤ q - r`, then
`n_b(q + 1 + r, 5) ≥ (2r + 1) · 2N(q) + K_𝓐 + K_𝓑`, with `N(q) = (q + 1)(q² + 1)`. -/

namespace BipartiteDD.LeanMaxx.D5

open SimpleGraph BipartiteDD Finset
open scoped Classical

set_option linter.unusedSectionVars false

variable {P L : Type*} [Membership P L] {ι V U : Type*}
  [Fintype P] [Fintype L] [Fintype ι] [Fintype V] [Fintype U]
  {D : Data P L ι V U} {q r : ℕ}

/-- **Theorem 3.5/3.6, bipartite degree-diameter form.** -/
theorem Hyp.isBipartiteDegDiam (H : Hyp D) (S : Surg D q r) (G : GQst P L q q) [Nonempty ι]
    (hT' : ∀ i j, D.T i j → ∀ x y : P ⊕ L, Reach D.X (.inl (x, i)) (.inl (y, j)) 5)
    (hgV : ∀ v v' : V, Reach D.X (.inr (.inl v)) (.inr (.inl v')) 4)
    (hgU : ∀ u u' : U, Reach D.X (.inr (.inr u)) (.inr (.inr u')) 4) :
    IsBipartiteDegDiam D.X (q + 1 + r) 5 :=
  ⟨H.colorable, fun w => S.degree_le H G w, H.ediam_le_five hT' hgV hgU⟩

/-- Transport to `Fin n`: a bipartite graph of maximum degree `q + 1 + r` and diameter `≤ 5` on
`(2r + 1)(|P| + |L|) + |V| + |U|` vertices. -/
theorem Hyp.exists_graph (H : Hyp D) (S : Surg D q r) (G : GQst P L q q) [Nonempty ι]
    (hT' : ∀ i j, D.T i j → ∀ x y : P ⊕ L, Reach D.X (.inl (x, i)) (.inl (y, j)) 5)
    (hgV : ∀ v v' : V, Reach D.X (.inr (.inl v)) (.inr (.inl v')) 4)
    (hgU : ∀ u u' : U, Reach D.X (.inr (.inr u)) (.inr (.inr u')) 4) :
    ∃ Y : SimpleGraph (Fin ((2 * r + 1) * (Fintype.card P + Fintype.card L) + Fintype.card V + Fintype.card U)),
      IsBipartiteDegDiam Y (q + 1 + r) 5 := by
  have hcard : Fintype.card (Vtx P L ι V U) =
      (2 * r + 1) * (Fintype.card P + Fintype.card L) + Fintype.card V + Fintype.card U := by
    rw [card_vtx, S.card_ι]; ring
  let e := Fintype.equivFinOfCardEq hcard
  exact ⟨D.X.comap e.symm, isBipartiteDegDiam_comap e (H.isBipartiteDegDiam S G hT' hgV hgU)⟩

/-- The same with the order written as in the note: `(2r + 1) · 2N(q) + K_𝓐 + K_𝓑`, `N(q) = (q+1)(q²+1)`. -/
theorem Hyp.exists_graph_N [Nonempty P] {G : GQ P L q}
    (uniq : ∀ (p : P) (l : L), p ∉ l → ∀ x y : P, x ∈ l → y ∈ l →
      (∃ m : L, p ∈ m ∧ x ∈ m) → (∃ m : L, p ∈ m ∧ y ∈ m) → x = y)
    (H : Hyp D) (S : Surg D q r) [Nonempty ι]
    (hT' : ∀ i j, D.T i j → ∀ x y : P ⊕ L, Reach D.X (.inl (x, i)) (.inl (y, j)) 5)
    (hgV : ∀ v v' : V, Reach D.X (.inr (.inl v)) (.inr (.inl v')) 4)
    (hgU : ∀ u u' : U, Reach D.X (.inr (.inr u)) (.inr (.inr u')) 4) :
    ∃ Y : SimpleGraph (Fin ((2 * r + 1) * (2 * ((q + 1) * (q ^ 2 + 1))) + Fintype.card V + Fintype.card U)),
      IsBipartiteDegDiam Y (q + 1 + r) 5 := by
  obtain ⟨Y, hY⟩ := H.exists_graph S G.toGQst hT' hgV hgU
  have hP := GQ.card_points G uniq
  have hL := GQ.card_pts_eq_card_lines G
  have : (2 * r + 1) * (Fintype.card P + Fintype.card L) = (2 * r + 1) * (2 * ((q + 1) * (q ^ 2 + 1))) := by
    rw [← hL, hP]; ring
  rw [← this]
  exact ⟨Y, hY⟩

end BipartiteDD.LeanMaxx.D5
