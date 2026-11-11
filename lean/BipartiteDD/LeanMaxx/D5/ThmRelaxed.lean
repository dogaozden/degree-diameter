import BipartiteDD.LeanMaxx.D5.ThmB

/-! # D = 5 formalisation, part 13: relaxed freed sets and the hub rule (Propositions 7.1–7.2, as (T'))

`research/theorems/D5_QUADRANGLE.md` §7. On an automorphic transition `i → j` (`M = ψ` on `A_i`, `ψ` an automorphism
of the incidence graph) the freed set `R ⊆ A_i` may contain pairs at distance two ("partners"), if

* (R1) every freed element has at most one partner,
* (R1h) for every ordered pair `(x, y)` of partners there is an `𝓐`-hub `g` whose slot at level `j` is `M y` and whose
  slot at level `i` is adjacent to `x` (Proposition 7.2: "the `𝓐`-hub of the slot `(ℓ, t)` sits at a point of the
  partner"; the slots are those of `Data.slotU`),

and the quadrangle has three neighbours at every element (`Base3`, orders `≥ 2`). Then the arc satisfies the
hypothesis (T') of Theorem 3.6: every vertex of level `i` is within `5` of every vertex of level `j` in `X_R^+`
(`Hyp.reach_relaxed`). Without the hubs the transition is not repaired in general (Proposition 7.1, not formalised).
Together with `Hyp.ediam_le_five` this is the mechanism that lets the seven-level graphs of §7 and §11 use relaxed
sets. -/

namespace BipartiteDD.LeanMaxx.D5

open SimpleGraph BipartiteDD

variable {P L : Type*} [Membership P L] {ι V U : Type*}

/-- Three different neighbours of every element (orders `s, t ≥ 2`). -/
def Base3 (P L : Type*) [Membership P L] : Prop :=
  ∀ x : P ⊕ L, ∃ y1 y2 y3, y1 ≠ y2 ∧ y1 ≠ y3 ∧ y2 ≠ y3 ∧ (incGraph P L).Adj x y1 ∧
    (incGraph P L).Adj x y2 ∧ (incGraph P L).Adj x y3

end BipartiteDD.LeanMaxx.D5

namespace BipartiteDD.GQst

open BipartiteDD.LeanMaxx.D5

theorem base3 {P L : Type*} [Membership P L] {s t : ℕ} (G : GQst P L (s + 2) (t + 2)) :
    Base3 P L := by
  rintro (p | l)
  · have h : 2 < Nat.card {l : L // p ∈ l} := by rw [G.lines_on_pt p]; omega
    have : Finite {l : L // p ∈ l} := Nat.finite_of_card_ne_zero (by omega)
    have := Fintype.ofFinite {l : L // p ∈ l}
    have h' : 2 < Fintype.card {l : L // p ∈ l} := by rw [Fintype.card_eq_nat_card]; exact h
    obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h'
    exact ⟨.inr a.1, .inr b.1, .inr c.1, by simpa using fun h => hab (Subtype.ext h),
      by simpa using fun h => hac (Subtype.ext h), by simpa using fun h => hbc (Subtype.ext h),
      incGraph_adj_inl_inr.2 a.2, incGraph_adj_inl_inr.2 b.2, incGraph_adj_inl_inr.2 c.2⟩
  · have h : 2 < Nat.card {p : P // p ∈ l} := by rw [G.pts_on_line l]; omega
    have : Finite {p : P // p ∈ l} := Nat.finite_of_card_ne_zero (by omega)
    have := Fintype.ofFinite {p : P // p ∈ l}
    have h' : 2 < Fintype.card {p : P // p ∈ l} := by rw [Fintype.card_eq_nat_card]; exact h
    obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h'
    exact ⟨.inl a.1, .inl b.1, .inl c.1, by simpa using fun h => hab (Subtype.ext h),
      by simpa using fun h => hac (Subtype.ext h), by simpa using fun h => hbc (Subtype.ext h),
      incGraph_adj_inr_inl.2 a.2, incGraph_adj_inr_inl.2 b.2, incGraph_adj_inr_inl.2 c.2⟩

end BipartiteDD.GQst

namespace BipartiteDD.LeanMaxx.D5

open SimpleGraph BipartiteDD

variable {P L : Type*} [Membership P L] {ι V U : Type*}

theorem bool_ne {a b : Bool} (h : ¬ a = b) : a = !b := by cases a <;> cases b <;> simp_all

namespace Hyp

variable {D : Data P L ι V U} (H : Hyp D)
include H

/-- A level step in `X`. -/
theorem lvl_adj (i : ι) {x y : P ⊕ L} (h : (incGraph P L).Adj x y) :
    Reach D.X (.inl (x, i)) (.inl (y, i)) 1 :=
  Reach.adj ((D.lvl i).map_rel h)

/-- The hub route of Proposition 7.2: `(x, i) → slot → hub → (M z, j) → (v, j)` has length `4`. -/
theorem hub_route {i j : ι} (g : U) {x z w : P ⊕ L} (ψ : incGraph P L ≃g incGraph P L)
    (hgj : D.slotU g j = ψ z) (hgx : (incGraph P L).Adj (D.slotU g i) x) (hzw : (incGraph P L).Adj z w) :
    Reach D.X (.inl (x, i)) (.inl (ψ w, j)) 4 := by
  have e1 := H.lvl_adj i hgx.symm
  have e2 := (Reach.adj (D.adj_slotU g i)).symm
  have e3 := Reach.adj (D.adj_slotU g j)
  rw [hgj] at e3
  have e4 := H.lvl_adj j (ψ.map_adj_iff.2 hzw)
  exact (((e1.trans e2).trans e3).trans e4)

/-- **Proposition 7.2 as (T').** Relaxed freed set + hub rule + three neighbours: every vertex of level `i` is within
`5` of every vertex of level `j` in `X_R^+`, for an automorphic arc. -/
theorem reach_relaxed {i j : ι} (hT : D.T i j) (B3 : Base3 P L)
    (hRA : ∀ x ∈ D.R i j, col x = D.τ i) (ψ : incGraph P L ≃g incGraph P L)
    (hψ : ∀ x, col x = D.τ i → D.M i j x = ψ x)
    (hR1 : ∀ x ∈ D.R i j, ∀ y ∈ D.R i j, ∀ y' ∈ D.R i j, Co x y → Co x y' → y = y')
    (hR1h : ∀ x ∈ D.R i j, ∀ y ∈ D.R i j, Co x y →
      ∃ g : U, D.slotU g j = D.M i j y ∧ (incGraph P L).Adj (D.slotU g i) x)
    (u v : P ⊕ L) : Reach D.X (.inl (u, i)) (.inl (v, j)) 5 := by
  have hij := H.irrefl i j hT
  have shift : ∀ {a : P ⊕ L}, col a = D.τ i → a ∉ D.R i j →
      Reach D.X (.inl (a, i)) (.inl (ψ a, j)) 1 := fun {a} ha haR => by
    have := Reach.adj (D.adj_shift hij hT ha haR)
    rwa [hψ a ha] at this
  -- an element of `R` reaches every element of `A_j` within `4`
  have CL : ∀ x ∈ D.R i j, ∀ v' : P ⊕ L, col v' = D.τ j → Reach D.X (.inl (x, i)) (.inl (v', j)) 4 := by
    intro x hx v' hv'
    have hw : col (ψ.symm v') = !D.τ i := H.psi_symm_B hT ψ hψ hv'
    have hxA := hRA x hx
    obtain ⟨z, hco, hzw⟩ := H.base.cover x (ψ.symm v') (by rw [hxA, hw]; cases D.τ i <;> simp)
    have hzA : col z = D.τ i := by rw [← hco.col_eq, hxA]
    by_cases hzR : z ∈ D.R i j
    · obtain ⟨g, hg1, hg2⟩ := hR1h x hx z hzR hco
      rw [hψ z hzA] at hg1
      have := H.hub_route g ψ hg1 hg2 hzw
      simpa using this
    · have e1 := (hco.reach.map (D.lvl i))
      have e2 := shift hzA hzR
      have e3 := H.lvl_adj j (ψ.map_adj_iff.2 hzw)
      simp only [RelIso.apply_symm_apply] at e3
      exact (((e1.trans e2).trans e3)).mono (by norm_num)
  by_cases hu : col u = D.τ i
  · by_cases huR : u ∈ D.R i j
    · by_cases hv : col v = D.τ j
      · exact (CL u huR v hv).mono (by norm_num)
      · obtain ⟨w, -, -, hw, -⟩ := H.base.two v
        have hwc : col w = D.τ j := by
          rw [col_adj_not hw.symm, bool_ne hv]; simp
        exact ((CL u huR w hwc).trans (H.lvl_adj j hw.symm)).mono (by norm_num)
    · have e1 := Reach.adj (D.adj_shift hij hT hu huR)
      exact (e1.trans (H.level _ v j)).mono (by norm_num)
  · have hu' : col u = !D.τ i := bool_ne hu
    by_cases hv : col v = D.τ j
    · -- some neighbour of `ψ⁻¹ v` is not freed
      have hw : col (ψ.symm v) = !D.τ i := H.psi_symm_B hT ψ hψ hv
      obtain ⟨a1, a2, a3, h12, h13, h23, d1, d2, d3⟩ := B3 (ψ.symm v)
      have hgood : ∃ a, (incGraph P L).Adj (ψ.symm v) a ∧ a ∉ D.R i j := by
        by_contra hcon
        push_neg at hcon
        have r1 := hcon a1 d1
        have r2 := hcon a2 d2
        have r3 := hcon a3 d3
        have c12 : Co a1 a2 := ⟨h12, _, d1.symm, d2⟩
        have c13 : Co a1 a3 := ⟨h13, _, d1.symm, d3⟩
        exact h23 (hR1 a1 r1 a2 r2 a3 r3 c12 c13)
      obtain ⟨a, hadj, haR⟩ := hgood
      have haA : col a = D.τ i := by rw [col_adj_not hadj.symm, hw]; cases D.τ i <;> simp
      have e1 := (H.base.odd3 u a (by rw [hu', haA]; cases D.τ i <;> simp)).map (D.lvl i)
      have e2 := shift haA haR
      have e3 := H.lvl_adj j (ψ.map_adj_iff.2 hadj.symm)
      simp only [RelIso.apply_symm_apply] at e3
      exact (((e1.trans e2).trans e3))
    · have hv' : col v = !D.τ j := bool_ne hv
      set x' := (D.M i j).symm v with hx'
      have hxA : col x' = D.τ i := H.onto i j hT v hv'
      have hMx : D.M i j x' = v := by simp [hx']
      by_cases hx'R : x' ∈ D.R i j
      · obtain ⟨z, hco, hzu⟩ := H.base.cover x' u (by rw [hxA, hu']; cases D.τ i <;> simp)
        have hzA : col z = D.τ i := by rw [← hco.col_eq, hxA]
        by_cases hzR : z ∈ D.R i j
        · obtain ⟨g, hg1, hg2⟩ := hR1h z hzR x' hx'R hco.symm
          -- `u` and `slotU g i` are both adjacent to `z`
          have e1 := (Reach.two hzu.symm hg2.symm).map (D.lvl i)
          have e2 := (Reach.adj (D.adj_slotU g i)).symm
          have e3 := Reach.adj (D.adj_slotU g j)
          rw [hg1, hMx] at e3
          exact (((e1.trans e2).trans e3)).mono (by norm_num)
        · have e1 := H.lvl_adj i hzu.symm
          have e2 := shift hzA hzR
          have hco' : Co (ψ x') (ψ z) := (Co.map_iff ψ).2 hco
          have hvψ : v = ψ x' := by rw [← hMx, hψ x' hxA]
          have e3 := hco'.symm.reach.map (D.lvl j)
          rw [← hvψ] at e3
          exact (((e1.trans e2).trans e3)).mono (by norm_num)
      · have e1 := (H.base.odd3 u x' (by rw [hu', hxA]; cases D.τ i <;> simp)).map (D.lvl i)
        have e2 := Reach.adj (D.adj_shift hij hT hxA hx'R)
        rw [hMx] at e2
        exact (e1.trans e2).mono (by norm_num)

end Hyp

end BipartiteDD.LeanMaxx.D5
