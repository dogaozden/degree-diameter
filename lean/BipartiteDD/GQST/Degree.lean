import BipartiteDD.GQST.Blowup
import Mathlib.Tactic.Linarith

/-! Group GQST, part 4: degrees in the weighted copy graph. Each neighbourhood is contained in the range
of a map from an explicit finite type, whose cardinality is bounded:
- original point `p`: the `t + 1` original lines through `p`, and one copy per (line through `p`, copy
  index); total `t + 1 + ∑_{l ∋ p} m l ≤ t + 1 + b`;
- copy of a point `x`: the `t + 1` original lines through `x`;
- original line `l`: the `s + 1` original points on `l`, and one copy per (point `x` on `l`, copy index);
  total `s + 1 + ∑_{x ∈ l} w x ≤ s + 1 + a`;
- copy of a line: the `s + 1` original points on it.
Hence every vertex has degree at most `max (s + 1 + a) (t + 1 + b)`. -/

namespace BipartiteDD.GQST

open SimpleGraph
open scoped Classical

variable {P L : Type*} [Membership P L]

theorem ncard_nbr_pt [Fintype P] [Fintype L] {s t : ℕ} (G : GQst P L s t) (w : P → ℕ) (m : L → ℕ)
    (b : ℕ) (hm : ∀ p : P, ∑ l ∈ Finset.univ.filter (fun l => p ∈ l), m l ≤ b) (p : P) :
    ((blowup P L w m).neighborSet (.inl (.inl p))).ncard ≤ t + 1 + b := by
  refine (GQ4.ncard_le_of_subset_range _
    (fun d : {l : L // p ∈ l} ⊕ (Σ l : {l : L // p ∈ l}, Fin (m l.1)) =>
      (match d with
        | .inl l => .inr (.inl l.1)
        | .inr z => .inr (.inr ⟨z.1.1, z.2⟩) :
        (P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l)))) ?_).trans ?_
  · rintro y hy
    have hy2 : (incGraph P L).Adj (under (w := w) (m := m) (.inl (.inl p))) (under y) ∧
        (isOrig (w := w) (m := m) (.inl (.inl p)) ∨ isOrig y) :=
      blowup_adj_iff.1 ((mem_neighborSet _ _ _).1 hy)
    rcases y with (q | ⟨x, i⟩) | (l | ⟨l, k⟩)
    · exact (incGraph_not_adj_inl_inl hy2.1).elim
    · exact (incGraph_not_adj_inl_inl hy2.1).elim
    · exact ⟨.inl ⟨l, incGraph_adj_inl_inr.1 hy2.1⟩, rfl⟩
    · exact ⟨.inr ⟨⟨l, incGraph_adj_inl_inr.1 hy2.1⟩, k⟩, rfl⟩
  · have hc : Fintype.card {l : L // p ∈ l} = t + 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact G.lines_on_pt p
    have hsum : ∑ l : {l : L // p ∈ l}, m l.1 = ∑ l ∈ Finset.univ.filter (fun l => p ∈ l), m l :=
      (Finset.sum_subtype (Finset.univ.filter (fun l => p ∈ l)) (by simp) m).symm
    simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin, hc, hsum]
    have := hm p
    omega

theorem ncard_nbr_pt_copy [Fintype P] [Fintype L] {s t : ℕ} (G : GQst P L s t) (w : P → ℕ)
    (m : L → ℕ) (x : P) (i : Fin (w x)) :
    ((blowup P L w m).neighborSet (.inl (.inr ⟨x, i⟩))).ncard ≤ t + 1 := by
  refine (GQ4.ncard_le_of_subset_range _
    (fun l : {l : L // x ∈ l} => (.inr (.inl l.1) :
      (P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l)))) ?_).trans ?_
  · rintro y hy
    have hy2 : (incGraph P L).Adj (under (w := w) (m := m) (.inl (.inr ⟨x, i⟩))) (under y) ∧
        (isOrig (w := w) (m := m) (.inl (.inr ⟨x, i⟩)) ∨ isOrig y) :=
      blowup_adj_iff.1 ((mem_neighborSet _ _ _).1 hy)
    rcases y with (q | ⟨x', i'⟩) | (l | ⟨l, k⟩)
    · exact (incGraph_not_adj_inl_inl hy2.1).elim
    · exact (incGraph_not_adj_inl_inl hy2.1).elim
    · exact ⟨⟨l, incGraph_adj_inl_inr.1 hy2.1⟩, rfl⟩
    · exact (hy2.2.elim (fun h => by simp [isOrig] at h) (fun h => by simp [isOrig] at h))
  · have hc : Fintype.card {l : L // x ∈ l} = t + 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact G.lines_on_pt x
    rw [hc]

theorem ncard_nbr_line [Fintype P] [Fintype L] {s t : ℕ} (G : GQst P L s t) (w : P → ℕ)
    (m : L → ℕ) (a : ℕ) (hw : ∀ l : L, ∑ p ∈ Finset.univ.filter (fun p => p ∈ l), w p ≤ a) (l : L) :
    ((blowup P L w m).neighborSet (.inr (.inl l))).ncard ≤ s + 1 + a := by
  refine (GQ4.ncard_le_of_subset_range _
    (fun d : {p : P // p ∈ l} ⊕ (Σ x : {x : P // x ∈ l}, Fin (w x.1)) =>
      (match d with
        | .inl p => .inl (.inl p.1)
        | .inr z => .inl (.inr ⟨z.1.1, z.2⟩) :
        (P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l)))) ?_).trans ?_
  · rintro y hy
    have hy2 : (incGraph P L).Adj (under (w := w) (m := m) (.inr (.inl l))) (under y) ∧
        (isOrig (w := w) (m := m) (.inr (.inl l)) ∨ isOrig y) :=
      blowup_adj_iff.1 ((mem_neighborSet _ _ _).1 hy)
    rcases y with (q | ⟨x, i⟩) | (l' | ⟨l', k⟩)
    · exact ⟨.inl ⟨q, incGraph_adj_inr_inl.1 hy2.1⟩, rfl⟩
    · have hx : x ∈ l := incGraph_adj_inr_inl.1 hy2.1
      exact ⟨.inr ⟨⟨x, hx⟩, i⟩, rfl⟩
    · exact (incGraph_not_adj_inr_inr hy2.1).elim
    · exact (incGraph_not_adj_inr_inr hy2.1).elim
  · have hc : Fintype.card {p : P // p ∈ l} = s + 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact G.pts_on_line l
    have hsum : ∑ x : {x : P // x ∈ l}, w x.1 = ∑ x ∈ Finset.univ.filter (fun x => x ∈ l), w x :=
      (Finset.sum_subtype (Finset.univ.filter (fun x => x ∈ l)) (by simp) w).symm
    simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin, hc, hsum]
    have := hw l
    omega

theorem ncard_nbr_line_copy [Fintype P] [Fintype L] {s t : ℕ} (G : GQst P L s t) (w : P → ℕ)
    (m : L → ℕ) (l : L) (k : Fin (m l)) :
    ((blowup P L w m).neighborSet (.inr (.inr ⟨l, k⟩))).ncard ≤ s + 1 := by
  refine (GQ4.ncard_le_of_subset_range _
    (fun p : {p : P // p ∈ l} => (.inl (.inl p.1) :
      (P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l)))) ?_).trans ?_
  · rintro y hy
    have hy2 : (incGraph P L).Adj (under (w := w) (m := m) (.inr (.inr ⟨l, k⟩))) (under y) ∧
        (isOrig (w := w) (m := m) (.inr (.inr ⟨l, k⟩)) ∨ isOrig y) :=
      blowup_adj_iff.1 ((mem_neighborSet _ _ _).1 hy)
    rcases y with (q | ⟨x', i'⟩) | (l' | ⟨l', k'⟩)
    · exact ⟨⟨q, incGraph_adj_inr_inl.1 hy2.1⟩, rfl⟩
    · exact (hy2.2.elim (fun h => by simp [isOrig] at h) (fun h => by simp [isOrig] at h))
    · exact (incGraph_not_adj_inr_inr hy2.1).elim
    · exact (incGraph_not_adj_inr_inr hy2.1).elim
  · have hc : Fintype.card {p : P // p ∈ l} = s + 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact G.pts_on_line l
    rw [hc]

/-- Every vertex of the copy graph has degree at most `max (s + 1 + a) (t + 1 + b)`. -/
theorem blowup_degree [Fintype P] [Fintype L] {s t : ℕ} (G : GQst P L s t) (w : P → ℕ)
    (m : L → ℕ) (a b : ℕ)
    (hw : ∀ l : L, ∑ p ∈ Finset.univ.filter (fun p => p ∈ l), w p ≤ a)
    (hm : ∀ p : P, ∑ l ∈ Finset.univ.filter (fun l => p ∈ l), m l ≤ b)
    (v : (P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l))) :
    ((blowup P L w m).neighborSet v).ncard ≤ max (s + 1 + a) (t + 1 + b) := by
  have h1 := le_max_left (s + 1 + a) (t + 1 + b)
  have h2 := le_max_right (s + 1 + a) (t + 1 + b)
  rcases v with (p | ⟨x, i⟩) | (l | ⟨l, k⟩)
  · have := ncard_nbr_pt G w m b hm p
    omega
  · have := ncard_nbr_pt_copy G w m x i
    omega
  · have := ncard_nbr_line G w m a hw l
    omega
  · have := ncard_nbr_line_copy G w m l k
    omega

end BipartiteDD.GQST
