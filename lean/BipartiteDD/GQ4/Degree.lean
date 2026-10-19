import BipartiteDD.GQ4.Blowup
import Mathlib.Tactic.Linarith

/-! Group GQ4, part 5: degrees in the blow-up. Each neighbourhood is contained in the range of a map
from an explicit finite type, whose cardinality is bounded by `q + 1 + j`:
- original point `p`: the `q + 1` original lines through `p`, and one copy per (line through `p`, copy
  index); total `q + 1 + ∑_{l ∋ p} m l ≤ q + 1 + j`;
- copy of a point `x ∈ O`: the `q + 1` original lines through `x`;
- original line `l`: the `q + 1` original points on `l`, and `j` copies per point of `O` on `l`, at most
  one such point; total `≤ q + 1 + j`;
- copy of a line: the `q + 1` original points on it. -/

namespace BipartiteDD.GQ4

open SimpleGraph
open scoped Classical

variable {P L : Type*} [Membership P L]

/-- Every vertex of the blow-up has degree at most `q + 1 + j`. -/
theorem blowup_degree [Fintype P] [Fintype L] {q : ℕ} (G : GQ P L q) (O : Finset P)
    (hO : ∀ l : L, (O.filter (fun p => p ∈ l)).card ≤ 1) (j : ℕ) (m : L → ℕ)
    (hm : ∀ p : P, ∑ l ∈ Finset.univ.filter (fun l => p ∈ l), m l ≤ j)
    (v : (P ⊕ (O × Fin j)) ⊕ (L ⊕ Σ l, Fin (m l))) :
    ((blowup P L O j m).neighborSet v).ncard ≤ q + 1 + j := by
  rcases v with (p | ⟨x, i⟩) | (l | ⟨l, k⟩)
  · -- an original point `p`
    refine (ncard_le_of_subset_range _
      (fun d : {l : L // p ∈ l} ⊕ (Σ l : {l : L // p ∈ l}, Fin (m l.1)) =>
        (match d with
          | .inl l => .inr (.inl l.1)
          | .inr z => .inr (.inr ⟨z.1.1, z.2⟩) :
          (P ⊕ (O × Fin j)) ⊕ (L ⊕ Σ l, Fin (m l))))
      ?_).trans ?_
    · rintro y hy
      have hy2 : (incGraph P L).Adj (under (.inl (.inl p))) (under y) ∧
          (isOrig (.inl (.inl p) : (P ⊕ (O × Fin j)) ⊕ (L ⊕ Σ l, Fin (m l))) ∨ isOrig y) :=
        (blowup_adj_iff).1 ((mem_neighborSet _ _ _).1 hy)
      rcases y with (q | ⟨x, i⟩) | (l | ⟨l, k⟩)
      · exact (incGraph_not_adj_inl_inl hy2.1).elim
      · exact (incGraph_not_adj_inl_inl hy2.1).elim
      · exact ⟨.inl ⟨l, incGraph_adj_inl_inr.1 hy2.1⟩, rfl⟩
      · exact ⟨.inr ⟨⟨l, incGraph_adj_inl_inr.1 hy2.1⟩, k⟩, rfl⟩
    · have hc : Fintype.card {l : L // p ∈ l} = q + 1 := by
        rw [← Nat.card_eq_fintype_card]
        exact G.lines_on_pt p
      have hsum : ∑ l : {l : L // p ∈ l}, m l.1 = ∑ l ∈ Finset.univ.filter (fun l => p ∈ l), m l :=
        (Finset.sum_subtype (Finset.univ.filter (fun l => p ∈ l)) (by simp) m).symm
      simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin, hc, hsum]
      have := hm p
      omega
  · -- a copy of a point `x` of `O`: adjacent to the original lines through `x`
    refine (ncard_le_of_subset_range _
      (fun l : {l : L // x.1 ∈ l} => (.inr (.inl l.1) :
          (P ⊕ (O × Fin j)) ⊕ (L ⊕ Σ l, Fin (m l))))
      ?_).trans ?_
    · rintro y hy
      have hy2 : (incGraph P L).Adj (under (.inl (.inr (x, i)))) (under y) ∧
          (isOrig (.inl (.inr (x, i)) : (P ⊕ (O × Fin j)) ⊕ (L ⊕ Σ l, Fin (m l))) ∨ isOrig y) :=
        (blowup_adj_iff).1 ((mem_neighborSet _ _ _).1 hy)
      rcases y with (q | ⟨x', i'⟩) | (l | ⟨l, k⟩)
      · exact (incGraph_not_adj_inl_inl hy2.1).elim
      · exact (hy2.2.elim (fun h => by simp [isOrig] at h) (fun h => by simp [isOrig] at h))
      · exact ⟨⟨l, incGraph_adj_inl_inr.1 hy2.1⟩, rfl⟩
      · exact (hy2.2.elim (fun h => by simp [isOrig] at h) (fun h => by simp [isOrig] at h))
    · have hc : Fintype.card {l : L // x.1 ∈ l} = q + 1 := by
        rw [← Nat.card_eq_fintype_card]
        exact G.lines_on_pt x.1
      rw [hc]
      omega
  · -- an original line `l`
    refine (ncard_le_of_subset_range _
      (Sum.elim
        (fun p : {p : P // p ∈ l} => (.inl (.inl p.1) :
          (P ⊕ (O × Fin j)) ⊕ (L ⊕ Σ l, Fin (m l))))
        (fun z : {x : P // x ∈ O.filter (fun x => x ∈ l)} × Fin j => (.inl (.inr
          (⟨z.1.1, (Finset.mem_filter.1 z.1.2).1⟩, z.2)) :
          (P ⊕ (O × Fin j)) ⊕ (L ⊕ Σ l, Fin (m l)))))
      ?_).trans ?_
    · rintro y hy
      have hy2 : (incGraph P L).Adj (under (.inr (.inl l))) (under y) ∧
          (isOrig (.inr (.inl l) : (P ⊕ (O × Fin j)) ⊕ (L ⊕ Σ l, Fin (m l))) ∨ isOrig y) :=
        (blowup_adj_iff).1 ((mem_neighborSet _ _ _).1 hy)
      rcases y with (q | ⟨x', i'⟩) | (l' | ⟨l', k⟩)
      · exact ⟨.inl ⟨q, incGraph_adj_inr_inl.1 hy2.1⟩, rfl⟩
      · have hmem : x'.1 ∈ O.filter (fun x => x ∈ l) :=
          Finset.mem_filter.2 ⟨x'.2, incGraph_adj_inr_inl.1 hy2.1⟩
        exact ⟨.inr (⟨x'.1, hmem⟩, i'), rfl⟩
      · exact (incGraph_not_adj_inr_inr hy2.1).elim
      · exact (incGraph_not_adj_inr_inr hy2.1).elim
    · have hc : Fintype.card {p : P // p ∈ l} = q + 1 := by
        rw [← Nat.card_eq_fintype_card]
        exact G.pts_on_line l
      have hcard : Fintype.card {x : P // x ∈ O.filter (fun x => x ∈ l)} ≤ 1 := by
        rw [Fintype.card_coe]
        exact hO l
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hc]
      have := Nat.mul_le_mul_right j hcard
      rw [one_mul] at this
      linarith
  · -- a copy of a line `l`: adjacent to the original points on `l`
    refine (ncard_le_of_subset_range _
      (fun p : {p : P // p ∈ l} => (.inl (.inl p.1) :
          (P ⊕ (O × Fin j)) ⊕ (L ⊕ Σ l, Fin (m l))))
      ?_).trans ?_
    · rintro y hy
      have hy2 : (incGraph P L).Adj (under (.inr (.inr ⟨l, k⟩))) (under y) ∧
          (isOrig (.inr (.inr ⟨l, k⟩) : (P ⊕ (O × Fin j)) ⊕ (L ⊕ Σ l, Fin (m l))) ∨ isOrig y) :=
        (blowup_adj_iff).1 ((mem_neighborSet _ _ _).1 hy)
      rcases y with (q | ⟨x', i'⟩) | (l' | ⟨l', k'⟩)
      · exact ⟨⟨q, incGraph_adj_inr_inl.1 hy2.1⟩, rfl⟩
      · exact (hy2.2.elim (fun h => by simp [isOrig] at h) (fun h => by simp [isOrig] at h))
      · exact (incGraph_not_adj_inr_inr hy2.1).elim
      · exact (incGraph_not_adj_inr_inr hy2.1).elim
    · have hc : Fintype.card {p : P // p ∈ l} = q + 1 := by
        rw [← Nat.card_eq_fintype_card]
        exact G.pts_on_line l
      rw [hc]
      omega

end BipartiteDD.GQ4
