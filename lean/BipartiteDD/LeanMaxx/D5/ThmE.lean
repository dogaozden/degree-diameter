import BipartiteDD.LeanMaxx.D5.ThmA

/-! # D = 5 formalisation, part 7: Theorem E (the exact criterion for one transition)

`research/theorems/D5_QUADRANGLE.md` §4. For an arc `i → j` with freed set `R = D.R i j ⊆ A_i`, `R ≠ ∅`:
the transition is repaired (condition (3.1), `Data.Repaired`) **if and only if**

* (E2) for every `x ∈ R`, every element of `A_j` is adjacent to `M a` for some `a ∈ Γ₂(x) ∖ R`;
* (E3) for every `x ∈ R`, every element of `B_i` is adjacent to some `a ∉ R` with `M a ∈ Γ₂(M x)`.

Only the base facts of §1.1 and the bipartite parity of `I` are used, so the theorem holds for any quadrangle
with `s, t ≥ 1`. -/

namespace BipartiteDD.LeanMaxx.D5

open SimpleGraph BipartiteDD

variable {P L : Type*} [Membership P L] {ι V U : Type*}

/-- (E2) for the arc `i → j`. -/
def Data.E2 (D : Data P L ι V U) (i j : ι) : Prop :=
  ∀ x ∈ D.R i j, ∀ y : P ⊕ L, col y = D.τ j →
    ∃ a, Co x a ∧ a ∉ D.R i j ∧ (incGraph P L).Adj (D.M i j a) y

/-- (E3) for the arc `i → j`. -/
def Data.E3 (D : Data P L ι V U) (i j : ι) : Prop :=
  ∀ x ∈ D.R i j, ∀ b : P ⊕ L, col b = !D.τ i →
    ∃ a, a ∉ D.R i j ∧ (incGraph P L).Adj b a ∧ Co (D.M i j x) (D.M i j a)

/-- Walks between elements of one colour: length `0` (equal elements) or at least `2`, and even. -/
theorem walk_same {x y : P ⊕ L} (w : (incGraph P L).Walk x y) (hc : col x = col y) (hne : x ≠ y) :
    2 ≤ w.length ∧ w.length % 2 = 0 := by
  have hp := (walk_parity w).2 hc
  have h0 : w.length ≠ 0 := fun h0 => hne (Walk.eq_of_length_eq_zero h0)
  omega

/-- Walks between elements of different colours have odd length. -/
theorem walk_diff {x y : P ⊕ L} (w : (incGraph P L).Walk x y) (hc : col x ≠ col y) :
    w.length % 2 = 1 := by
  have hp := walk_parity w
  have : ¬ w.length % 2 = 0 := fun h => hc (hp.1 h)
  omega

namespace Hyp

variable {D : Data P L ι V U} (H : Hyp D)
include H

/-- **Theorem E**, the direction "repaired ⇒ (E2)". -/
theorem E2_of_repaired {i j : ι} (hT : D.T i j) (hRA : ∀ x ∈ D.R i j, col x = D.τ i)
    (hr : D.Repaired i j) : D.E2 i j := by
  intro x hx y hy
  obtain ⟨a, haA, haR, m, n, hmn, ⟨w1, hw1⟩, ⟨w2, hw2⟩⟩ := hr x y
  have hxa : x ≠ a := fun h => haR (h ▸ hx)
  have hca : col x = col a := by rw [hRA x hx, haA]
  have hc2 : col (D.M i j a) ≠ col y := by
    rw [H.maps i j hT a haA, hy]; cases D.τ j <;> simp
  obtain ⟨h1, h1'⟩ := walk_same w1 hca hxa
  have h2 := walk_diff w2 hc2
  have hl : w1.length = 2 := by omega
  have hl2 : w2.length = 1 := by omega
  refine ⟨a, Reach.co_of_two hxa hca ⟨w1, hl.le⟩, haR, ?_⟩
  exact Reach.adj_of_one hc2 ⟨w2, hl2.le⟩

/-- **Theorem E**, the direction "repaired ⇒ (E3)". -/
theorem E3_of_repaired {i j : ι} (hT : D.T i j) (hRA : ∀ x ∈ D.R i j, col x = D.τ i)
    (hr : D.Repaired i j) : D.E3 i j := by
  intro x hx b hb
  obtain ⟨a, haA, haR, m, n, hmn, ⟨w1, hw1⟩, ⟨w2, hw2⟩⟩ := hr b (D.M i j x)
  have hxA := hRA x hx
  have hxa : D.M i j a ≠ D.M i j x := fun h => haR (by rw [(D.M i j).injective h]; exact hx)
  have hc1 : col b ≠ col a := by rw [hb, haA]; cases D.τ i <;> simp
  have hca : col (D.M i j a) = col (D.M i j x) := by
    rw [H.maps i j hT a haA, H.maps i j hT x hxA]
  have h1 := walk_diff w1 hc1
  obtain ⟨h2, h2'⟩ := walk_same w2 hca hxa
  have hl : w2.length = 2 := by omega
  have hl1 : w1.length = 1 := by omega
  refine ⟨a, haR, Reach.adj_of_one hc1 ⟨w1, hl1.le⟩, ?_⟩
  exact (Reach.co_of_two hxa hca ⟨w2, hl.le⟩).symm

/-- **Theorem E**, the direction "(E2) and (E3) ⇒ repaired" (for `R ≠ ∅`). -/
theorem repaired_of_E {i j : ι} (hT : D.T i j) (hRA : ∀ x ∈ D.R i j, col x = D.τ i)
    (hne : (D.R i j).Nonempty) (h2 : D.E2 i j) (h3 : D.E3 i j) : D.Repaired i j := by
  obtain ⟨x0, hx0⟩ := hne
  intro u v
  by_cases hu : col u = D.τ i
  · by_cases huR : u ∈ D.R i j
    · by_cases hv : col v = D.τ j
      · obtain ⟨a, hco, haR, hadj⟩ := h2 u huR v hv
        refine ⟨a, ?_, haR, 2, 1, by norm_num, hco.reach, Reach.adj hadj⟩
        rw [← hco.col_eq, hu]
      · obtain ⟨w, -, -, hw, -⟩ := H.base.two v
        have hwcol : col w = D.τ j := by
          rw [col_adj_not hw.symm]; cases h : col v <;> cases h' : D.τ j <;> simp_all
        obtain ⟨a, hco, haR, hadj⟩ := h2 u huR w hwcol
        refine ⟨a, ?_, haR, 2, 2, by norm_num, hco.reach, (Reach.adj hadj).trans (Reach.adj hw.symm)⟩
        rw [← hco.col_eq, hu]
    · exact ⟨u, hu, huR, 0, 4, by norm_num, Reach.refl _ _, H.base.all4 _ _⟩
  · have hu' : col u = !D.τ i := by cases h1 : col u <;> cases h2 : D.τ i <;> simp_all
    by_cases hv : col v = D.τ j
    · obtain ⟨a, hco, haR, hadj⟩ := h2 x0 hx0 v hv
      have haA : col a = D.τ i := by rw [← hco.col_eq, hRA x0 hx0]
      refine ⟨a, haA, haR, 3, 1, by norm_num, H.base.odd3 _ _ ?_, Reach.adj hadj⟩
      rw [hu', haA]; cases D.τ i <;> simp
    · have hv' : col v = !D.τ j := by cases h1 : col v <;> cases h2 : D.τ j <;> simp_all
      set a := (D.M i j).symm v with ha
      have haA : col a = D.τ i := H.onto i j hT v hv'
      have hMa : D.M i j a = v := by simp [ha]
      by_cases haR : a ∈ D.R i j
      · obtain ⟨a', haR', hadj, hco⟩ := h3 a haR u hu'
        have haA' : col a' = D.τ i := by
          have := col_adj_not hadj; rw [hu'] at this; cases h : col a' <;> cases h' : D.τ i <;> simp_all
        refine ⟨a', haA', haR', 1, 2, by norm_num, Reach.adj hadj, ?_⟩
        rw [← hMa]; exact hco.symm.reach
      · refine ⟨a, haA, haR, 3, 0, by norm_num, H.base.odd3 _ _ ?_, by rw [hMa]; exact Reach.refl _ _⟩
        rw [hu', haA]; cases D.τ i <;> simp

/-- **Theorem E.** For an arc `i → j` with a nonempty freed set `R ⊆ A_i`: repaired ⟺ (E2) ∧ (E3). -/
theorem repaired_iff_E {i j : ι} (hT : D.T i j) (hRA : ∀ x ∈ D.R i j, col x = D.τ i)
    (hne : (D.R i j).Nonempty) : D.Repaired i j ↔ D.E2 i j ∧ D.E3 i j :=
  ⟨fun hr => ⟨H.E2_of_repaired hT hRA hr, H.E3_of_repaired hT hRA hr⟩,
   fun h => H.repaired_of_E hT hRA hne h.1 h.2⟩

end Hyp

end BipartiteDD.LeanMaxx.D5
