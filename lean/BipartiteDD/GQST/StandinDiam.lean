import BipartiteDD.GQST.Standin
import BipartiteDD.GQST.Defs

/-! Group GQST, part 7: the stand-in graph has diameter at most `4`. Proof of `research/NOTE.md`, Section 2.

Every distance is realised by an explicit walk of length at most `4`, using the adjacencies of `Standin`:
- two point-side vertices (original or copies): length at most `4`, through original lines and points only;
- a point-side vertex and an original line: length at most `3`;
- a point-side vertex and a line copy: length at most `3`, through the stand-in of a point of the copy's line;
- two original lines: length at most `4`, through original points only;
- an original line and a line copy: length at most `4`, through the stand-in of a point of the copy's line;
- two line copies: length at most `4`, through stand-ins of a common line. -/

namespace BipartiteDD.GQST

open SimpleGraph
open scoped Classical

variable {P L : Type*} [Membership P L] {s t : ℕ}
variable {w : P → ℕ} {m : L → ℕ}
  {σ : (c : Σ l, Fin (m l)) → (p : P) → p ∈ c.1 → Fin (w p + 1)}

/-- Two point-side vertices are at distance at most `4`. -/
theorem edist_pt_pt (G : GQst P L s t) (x y : P ⊕ Σ p, Fin (w p)) :
    (standin P L w m σ).edist (.inl x) (.inl y) ≤ 4 := by
  by_cases hc : ∃ ℓ : L, ptOf x ∈ ℓ ∧ ptOf y ∈ ℓ
  · obtain ⟨ℓ, hx, hy⟩ := hc
    exact (edist_le (Walk.cons (standin_adj_line_pt ℓ x hx).symm
      (Walk.cons (standin_adj_line_pt ℓ y hy) Walk.nil))).trans (by norm_num)
  · push Not at hc
    obtain ⟨ℓ, hy⟩ := G.exists_line (ptOf y)
    have hx : ptOf x ∉ ℓ := fun h => hc ℓ h hy
    obtain ⟨x0, hx0, k, hk1, hk2⟩ := G.gq_ax (ptOf x) ℓ hx
    exact (edist_le (Walk.cons (standin_adj_line_pt k x hk1).symm
      (Walk.cons (standin_adj_line_pt k (.inl x0) hk2)
        (Walk.cons (standin_adj_line_pt ℓ (.inl x0) hx0).symm
          (Walk.cons (standin_adj_line_pt ℓ y hy) Walk.nil))))).trans (by simp)

/-- A point-side vertex and an original line are at distance at most `3`. -/
theorem edist_pt_LO (G : GQst P L s t) (x : P ⊕ Σ p, Fin (w p)) (ℓ : L) :
    (standin P L w m σ).edist (.inl x) (.inr (.inl ℓ)) ≤ 3 := by
  by_cases hx : ptOf x ∈ ℓ
  · exact (edist_le (Walk.cons (standin_adj_line_pt ℓ x hx).symm Walk.nil)).trans (by simp)
  · obtain ⟨x0, hx0, k, hk1, hk2⟩ := G.gq_ax (ptOf x) ℓ hx
    exact (edist_le (Walk.cons (standin_adj_line_pt k x hk1).symm
      (Walk.cons (standin_adj_line_pt k (.inl x0) hk2)
        (Walk.cons (standin_adj_line_pt ℓ (.inl x0) hx0).symm Walk.nil)))).trans (by simp)

/-- A point-side vertex and a line copy are at distance at most `3`. -/
theorem edist_pt_LC (G : GQst P L s t) (x : P ⊕ Σ p, Fin (w p)) (c : Σ l, Fin (m l)) :
    (standin P L w m σ).edist (.inl x) (.inr (.inr c)) ≤ 3 := by
  by_cases hx : ptOf x ∈ c.1
  · exact (edist_le (Walk.cons (standin_adj_line_pt c.1 x hx).symm
      (Walk.cons (standin_adj_line_pt c.1 (standVtx (ptOf x) (σ c (ptOf x) hx))
          (by rw [ptOf_standVtx]; exact hx))
        (Walk.cons (standin_adj_stand c (ptOf x) hx).symm Walk.nil)))).trans (by simp)
  · obtain ⟨x0, hx0, k, hk1, hk2⟩ := G.gq_ax (ptOf x) c.1 hx
    exact (edist_le (Walk.cons (standin_adj_line_pt k x hk1).symm
      (Walk.cons (standin_adj_line_pt k (standVtx x0 (σ c x0 hx0)) (by rw [ptOf_standVtx]; exact hk2))
        (Walk.cons (standin_adj_stand c x0 hx0).symm Walk.nil)))).trans (by simp)

/-- Two original lines are at distance at most `4`. -/
theorem edist_LO_LO (G : GQst P L s t) (ℓ n : L) :
    (standin P L w m σ).edist (.inr (.inl ℓ)) (.inr (.inl n)) ≤ 4 := by
  by_cases hc : ∃ p : P, p ∈ ℓ ∧ p ∈ n
  · obtain ⟨p, hp1, hp2⟩ := hc
    exact (edist_le (Walk.cons (standin_adj_line_pt ℓ (.inl p) hp1)
      (Walk.cons (standin_adj_line_pt n (.inl p) hp2).symm Walk.nil))).trans (by norm_num)
  · push Not at hc
    obtain ⟨p, hp⟩ := G.exists_pt ℓ
    obtain ⟨x0, hx0, k, hk1, hk2⟩ := G.gq_ax p n (hc p hp)
    exact (edist_le (Walk.cons (standin_adj_line_pt ℓ (.inl p) hp)
      (Walk.cons (standin_adj_line_pt k (.inl p) hk1).symm
        (Walk.cons (standin_adj_line_pt k (.inl x0) hk2)
          (Walk.cons (standin_adj_line_pt n (.inl x0) hx0).symm Walk.nil))))).trans (by simp)

/-- An original line and a line copy are at distance at most `4`. -/
theorem edist_LO_LC (G : GQst P L s t) (ℓ : L) (c : Σ l, Fin (m l)) :
    (standin P L w m σ).edist (.inr (.inl ℓ)) (.inr (.inr c)) ≤ 4 := by
  by_cases hc : ∃ r : P, r ∈ ℓ ∧ r ∈ c.1
  · obtain ⟨r, hr1, hr2⟩ := hc
    exact (edist_le (Walk.cons (standin_adj_line_pt ℓ (standVtx r (σ c r hr2))
        (by rw [ptOf_standVtx]; exact hr1))
      (Walk.cons (standin_adj_stand c r hr2).symm Walk.nil))).trans (by norm_num)
  · obtain ⟨r, hr⟩ := G.exists_pt c.1
    obtain ⟨u, hu, k, hk1, hk2⟩ := G.gq_ax r ℓ (fun h => hc ⟨r, h, hr⟩)
    exact (edist_le (Walk.cons (standin_adj_line_pt ℓ (.inl u) hu)
      (Walk.cons (standin_adj_line_pt k (.inl u) hk2).symm
        (Walk.cons (standin_adj_line_pt k (standVtx r (σ c r hr)) (by rw [ptOf_standVtx]; exact hk1))
          (Walk.cons (standin_adj_stand c r hr).symm Walk.nil))))).trans (by simp)

/-- Two line copies are at distance at most `4`. -/
theorem edist_LC_LC (G : GQst P L s t) (c d : Σ l, Fin (m l)) :
    (standin P L w m σ).edist (.inr (.inr c)) (.inr (.inr d)) ≤ 4 := by
  obtain ⟨u, hu⟩ := G.exists_pt c.1
  by_cases hud : u ∈ d.1
  · obtain ⟨k, hk⟩ := G.exists_line u
    exact (edist_le (Walk.cons (standin_adj_stand c u hu)
      (Walk.cons (standin_adj_line_pt k (standVtx u (σ c u hu)) (by rw [ptOf_standVtx]; exact hk)).symm
        (Walk.cons (standin_adj_line_pt k (standVtx u (σ d u hud)) (by rw [ptOf_standVtx]; exact hk))
          (Walk.cons (standin_adj_stand d u hud).symm Walk.nil))))).trans (by simp)
  · obtain ⟨x, hx, k, hk1, hk2⟩ := G.gq_ax u d.1 hud
    exact (edist_le (Walk.cons (standin_adj_stand c u hu)
      (Walk.cons (standin_adj_line_pt k (standVtx u (σ c u hu)) (by rw [ptOf_standVtx]; exact hk1)).symm
        (Walk.cons (standin_adj_line_pt k (standVtx x (σ d x hx)) (by rw [ptOf_standVtx]; exact hk2))
          (Walk.cons (standin_adj_stand d x hx).symm Walk.nil))))).trans (by simp)

/-- The stand-in graph has diameter at most `4`. -/
theorem standin_ediam (G : GQst P L s t) : (standin P L w m σ).ediam ≤ 4 := by
  rw [ediam_le_iff]
  rintro (x | l | c) (y | l' | c')
  · exact edist_pt_pt G x y
  · exact (edist_pt_LO G x l').trans (by norm_num)
  · exact (edist_pt_LC G x c').trans (by norm_num)
  · rw [edist_comm]
    exact (edist_pt_LO G y l).trans (by norm_num)
  · exact edist_LO_LO G l l'
  · exact edist_LO_LC G l c'
  · rw [edist_comm]
    exact (edist_pt_LC G y c).trans (by norm_num)
  · rw [edist_comm]
    exact edist_LO_LC G l' c
  · exact edist_LC_LC G c c'

end BipartiteDD.GQST
