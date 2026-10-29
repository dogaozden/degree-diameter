import BipartiteDD.LeanMaxx.Omega3.Balls

/-!
# Lemma 3.1 with the exact constant: `|B(z, 4) ∩ opp(t)| ≤ q⁴`

`Omega3/Balls.lean` proves `|{x ∈ opp t : dist z x ≤ 4}| ≤ q⁴ + 2q²`. The `q = 7` argument of §4 of
`research/theorems/OMEGA_REPAIR.md` (Lemma 4.2) has a margin of only a few vertices, so it needs the exact
constant. Here `card_ballOpp_four_le_exact` proves `≤ q⁴` for every centre `z` of the colour of `t`, in any
generalized hexagon of order `(q, q)` (`Hex`).

With the notation of `Omega3/Balls.lean` (`X2`, `X4`, `T3`) and the double count `X4_add`
(`|X4| + q |X2| = q |T3|`), the ball is `X4` (when `dist t z = 2`), `X2 ∪ X4` (`dist t z = 4`) or
`{z} ∪ X2 ∪ X4` (`dist t z = 6`), and the new inputs are

* `dist t z = 4`: `q² ≤ |X2|` (`X2_ge_four`) and `|T3| + q ≤ q (q + 1) q` (`T3_le_four`);
* `dist t z = 6`: `q² ≤ |X2| + 1` (`X2_ge_six`) and `|T3| + (q + 1) ≤ q (q + 1) q` (`T3_le_six`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace BipartiteDD.LeanMaxx.Omega45

open SimpleGraph Finset BipartiteDD.LeanMaxx.Omega2 BipartiteDD.LeanMaxx.Omega3

variable {β : Type*} [Fintype β] [DecidableEq β] {B : SimpleGraph β} [DecidableRel B.Adj]
  {κ : β → ZMod 2} {q : ℕ} {t z : β}

theorem pred_eq (H : Hex B κ q) {u v a b : β} {e : ℕ} (he : e ≤ 4) (hv : B.dist u v = e + 1)
    (ha : B.Adj v a) (hb : B.Adj v b) (hda : B.dist u a = e) (hdb : B.dist u b = e) : a = b :=
  pred_unique H.girth H.reach he hv ha hb hda hdb

/-! ### `|X2|` -/

/-- For `dist t z = 4`: `q²` vertices of `X2`. Each of the `q` neighbours `u` of `z` at distance `5` from `t`
has `q` neighbours opposite `t`, none equal to `z`, and these lie at distance `2` from `z`. -/
theorem X2_ge_four (H : Hex B κ q) (hzc : κ z = κ t) (hz : B.dist t z = 4) :
    q * q ≤ (X2 B t z).card := by
  set U := (B.neighborFinset z).filter fun u => B.dist t u = 5 with hU
  have h1 : U.card * q ≤ (X2 B t z).card * 1 := by
    refine Finset.card_mul_le_card_mul B.Adj (s := U) (t := X2 B t z) ?_ ?_
    · intro u hu
      rw [hU, Finset.mem_filter, mem_neighborFinset] at hu
      have hcard := card_opp_nbrs H hu.2
      have hsub : ((B.neighborFinset u).filter fun x => B.dist t x = 6) ⊆
          (X2 B t z).bipartiteAbove B.Adj u := by
        intro x hx
        rw [Finset.mem_filter, mem_neighborFinset] at hx
        rw [Finset.bipartiteAbove, Finset.mem_filter, mem_X2]
        refine ⟨⟨?_, hx.2⟩, hx.1⟩
        refine dist_two_of_nbrs H hu.1 hx.1 ?_ (hzc.trans (col_opp H hx.2))
        rintro rfl; omega
      have := Finset.card_le_card hsub
      omega
    · intro x hx
      rw [mem_X2] at hx
      have hsub : (U.bipartiteBelow B.Adj x) ⊆ (B.neighborFinset x).filter fun y => B.dist z y = 1 := by
        intro u hu
        rw [Finset.bipartiteBelow, Finset.mem_filter, hU, Finset.mem_filter, mem_neighborFinset] at hu
        rw [Finset.mem_filter, mem_neighborFinset]
        exact ⟨hu.2.symm, dist_eq_one_iff_adj.2 hu.1.1⟩
      have := Finset.card_le_card hsub
      have h3 := card_pred_nbrs H (t := z) (d := 1) (by omega) (y := x) (by omega)
      omega
  have h2 := card_nbrs_five H (Or.inl hz)
  calc q * q ≤ U.card * q := Nat.mul_le_mul_right _ h2
    _ ≤ (X2 B t z).card := by simpa using h1

/-- For `dist t z = 6`: `q² - 1 ≤ |X2|`. All `q + 1` neighbours of `z` are at distance `5` from `t`; each has
`q - 1` neighbours opposite `t` other than `z`. -/
theorem X2_ge_six (H : Hex B κ q) (hq : 1 ≤ q) (hzc : κ z = κ t) (hz : B.dist t z = 6) :
    q * q ≤ (X2 B t z).card + 1 := by
  set U := B.neighborFinset z with hU
  have h1 : U.card * (q - 1) ≤ (X2 B t z).card * 1 := by
    refine Finset.card_mul_le_card_mul B.Adj (s := U) (t := X2 B t z) ?_ ?_
    · intro u hu
      rw [hU, mem_neighborFinset] at hu
      have h5 := dist_five_of_adj_six H hz hu
      have hcard := card_opp_nbrs H h5
      have hsub : ((B.neighborFinset u).filter fun x => B.dist t x = 6).erase z ⊆
          (X2 B t z).bipartiteAbove B.Adj u := by
        intro x hx
        rw [Finset.mem_erase, Finset.mem_filter, mem_neighborFinset] at hx
        rw [Finset.bipartiteAbove, Finset.mem_filter, mem_X2]
        exact ⟨⟨dist_two_of_nbrs H hu hx.2.1 hx.1 (hzc.trans (col_opp H hx.2.2)), hx.2.2⟩, hx.2.1⟩
      have := Finset.card_le_card hsub
      have h2 : (((B.neighborFinset u).filter fun x => B.dist t x = 6).erase z).card ≥ q - 1 := by
        have := Finset.pred_card_le_card_erase (s := (B.neighborFinset u).filter fun x => B.dist t x = 6)
          (a := z)
        omega
      omega
    · intro x hx
      rw [mem_X2] at hx
      have hsub : (U.bipartiteBelow B.Adj x) ⊆ (B.neighborFinset x).filter fun y => B.dist z y = 1 := by
        intro u hu
        rw [Finset.bipartiteBelow, Finset.mem_filter, hU, mem_neighborFinset] at hu
        rw [Finset.mem_filter, mem_neighborFinset]
        exact ⟨hu.2.symm, dist_eq_one_iff_adj.2 hu.1⟩
      have := Finset.card_le_card hsub
      have h3 := card_pred_nbrs H (t := z) (d := 1) (by omega) (y := x) (by omega)
      omega
  rw [hU, card_neighborFinset_eq_degree, H.deg] at h1
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel, mul_one] at h1
  nlinarith

/-! ### `|T3|` -/

theorem T3_le_four (H : Hex B κ q) (hz : B.dist t z = 4) :
    (T3 B t z).card + q ≤ q * (q * (q + 1)) := by
  obtain ⟨b, hzb, hb⟩ := exists_pred H.reach (u := t) (v := z) (e := 3) (by omega)
  obtain ⟨c, hbc, hc⟩ := exists_pred H.reach (u := t) (v := b) (e := 2) (by omega)
  set W := (B.neighborFinset c).erase b with hW
  have hWc : W.card = q := by
    rw [hW, Finset.card_erase_of_mem ((mem_neighborFinset B c b).2 hbc.symm), card_neighborFinset_eq_degree,
      H.deg]; rfl
  have hWsph : W ⊆ sph B z 3 := by
    intro y hy
    rw [hW, Finset.mem_erase, mem_neighborFinset] at hy
    obtain ⟨hyb, hcy⟩ := hy
    rw [mem_sph]
    have hzb1 : B.dist z b = 1 := dist_eq_one_iff_adj.2 hzb
    have hbc1 : B.dist b c = 1 := dist_eq_one_iff_adj.2 hbc
    have hcy1 : B.dist c y = 1 := dist_eq_one_iff_adj.2 hcy
    have hle : B.dist z y ≤ 3 := by
      have h1 := dist_tri H z b y
      have h2 := dist_tri H b c y
      omega
    have hcol : κ z ≠ κ y := by
      have e1 := zmod2_eq_add_one (H.col z b hzb)
      have e2 := zmod2_eq_add_one (H.col b c hbc)
      have e3 := zmod2_eq_add_one (H.col c y hcy)
      rw [e3, e2, e1, zmod2_add_one_add_one]
      generalize κ z = s; revert s; decide
    have hodd := dist_odd_of_col H hcol
    have hne1 : B.dist z y ≠ 1 := by
      intro h1
      have hzy : B.Adj z y := dist_eq_one_iff_adj.1 h1
      -- distance of `y` from `t`
      have hty : B.dist t y = 1 ∨ B.dist t y = 3 := by
        have := nbr_dist H.col H.reach (u := t) hcy
        rcases this with h | h <;> omega
      rcases hty with h | h
      · have := dist_tri H t y z
        have e : B.dist y z = 1 := dist_eq_one_iff_adj.2 hzy.symm
        omega
      · exact hyb (pred_eq H (u := t) (v := z) (e := 3) (by omega) (by omega) hzy hzb h hb)
    obtain ⟨k, hk⟩ := hodd
    omega
  have hdisj : Disjoint (T3 B t z) W := by
    rw [Finset.disjoint_left]
    intro y hT hWy
    rw [mem_T3] at hT
    rw [hW, Finset.mem_erase, mem_neighborFinset] at hWy
    have := nbr_dist H.col H.reach (u := t) hWy.2
    omega
  have hsub : T3 B t z ∪ W ⊆ sph B z 3 := by
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · exact (Finset.mem_filter.1 hy).1
    · exact hWsph hy
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, card_sph_three H, hWc] at this
  omega

theorem T3_le_six (H : Hex B κ q) (hz : B.dist t z = 6) :
    (T3 B t z).card + (q + 1) ≤ q * (q * (q + 1)) := by
  set W := (sph B z 3).filter fun y => B.dist t y = 3 with hW
  have hdisj : Disjoint (T3 B t z) W := by
    rw [Finset.disjoint_left]
    intro y hT hWy
    rw [mem_T3] at hT
    rw [hW, Finset.mem_filter] at hWy
    omega
  have hsub : T3 B t z ∪ W ⊆ sph B z 3 := by
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · exact (Finset.mem_filter.1 hy).1
    · exact (Finset.mem_filter.1 hy).1
  have hW' : q + 1 ≤ W.card := by
    have hex : ∀ u ∈ B.neighborFinset z, ∃ w, w ∈ W ∧ ∃ v, B.Adj u v ∧ B.Adj v w ∧ B.dist t v = 4 := by
      intro u hu
      rw [mem_neighborFinset] at hu
      have h5 := dist_five_of_adj_six H hz hu
      obtain ⟨v, huv, hv⟩ := exists_pred H.reach (u := t) (v := u) (e := 4) (by omega)
      obtain ⟨w, hvw, hw⟩ := exists_pred H.reach (u := t) (v := v) (e := 3) (by omega)
      refine ⟨w, ?_, v, huv, hvw, hv⟩
      rw [hW, Finset.mem_filter, mem_sph]
      refine ⟨?_, hw⟩
      have hzu1 : B.dist z u = 1 := dist_eq_one_iff_adj.2 hu
      have huv1 : B.dist u v = 1 := dist_eq_one_iff_adj.2 huv
      have hvw1 : B.dist v w = 1 := dist_eq_one_iff_adj.2 hvw
      have hle : B.dist z w ≤ 3 := by
        have h1 := dist_tri H z u w
        have h2 := dist_tri H u v w
        omega
      have hge : 6 ≤ B.dist t w + B.dist w z := by
        have := dist_tri H t w z
        omega
      have : B.dist w z = B.dist z w := SimpleGraph.dist_comm
      omega
    choose! f hf using hex
    have hinj : Set.InjOn f (B.neighborFinset z : Set β) := by
      intro u hu u' hu' hff
      rw [Finset.mem_coe, mem_neighborFinset] at hu hu'
      obtain ⟨hW1, v, huv, hvw, hv⟩ := hf u (by rw [mem_neighborFinset]; exact hu)
      obtain ⟨hW2, v', huv', hvw', hv'⟩ := hf u' (by rw [mem_neighborFinset]; exact hu')
      rw [← hff] at hvw' hW2
      have hzw : B.dist z (f u) = 3 := by
        have := (Finset.mem_filter.1 hW1).1
        exact mem_sph.1 this
      have hzv : B.dist z v = 2 := by
        refine dist_two_of_nbrs H hu huv ?_ (col_eq_of_adj_adj H hu huv)
        rintro rfl; omega
      have hzv' : B.dist z v' = 2 := by
        refine dist_two_of_nbrs H hu' huv' ?_ (col_eq_of_adj_adj H hu' huv')
        rintro rfl; omega
      have hvv : v = v' :=
        pred_eq H (u := z) (v := f u) (e := 2) (by omega) (by omega) hvw.symm hvw'.symm hzv hzv'
      subst hvv
      exact pred_eq H (u := z) (v := v) (e := 1) (by omega) (by omega) huv.symm huv'.symm
        (dist_eq_one_iff_adj.2 hu) (dist_eq_one_iff_adj.2 hu')
    have hmaps : ∀ u ∈ B.neighborFinset z, f u ∈ W := fun u hu => (hf u hu).1
    have := Finset.card_le_card_of_injOn f hmaps hinj
    rw [card_neighborFinset_eq_degree, H.deg] at this
    exact this
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, card_sph_three H] at this
  omega

/-! ### The exact bound -/

/-- **Lemma 3.1 (exact constant).** At most `q⁴` vertices opposite `t` lie within distance `4` of a centre `z`
of the colour of `t`. -/
theorem card_ballOpp_four_le_exact (H : Hex B κ q) (hq : 1 ≤ q) (hzc : κ z = κ t) :
    (ballOpp B t z 4).card ≤ q ^ 4 := by
  have hid := X4_add (B := B) (t := t) (z := z) H
  have hcases : ∀ x ∈ ballOpp B t z 4, x = z ∨ (B.dist z x = 2 ∧ B.dist t x = 6) ∨
      (B.dist z x = 4 ∧ B.dist t x = 6) := by
    intro x hx
    by_cases hxz : x = z
    · exact Or.inl hxz
    · right
      have he := ballOpp_even H hzc hx
      have hle := (mem_ballOpp.1 hx).2
      have h6 := (mem_ballOpp.1 hx).1
      obtain ⟨k, hk⟩ := he
      have h0 : B.dist z x ≠ 0 := fun h0 => hxz ((H.reach z x).dist_eq_zero_iff.1 h0).symm
      have : B.dist z x = 2 ∨ B.dist z x = 4 := by omega
      rcases this with h | h
      · exact Or.inl ⟨h, h6⟩
      · exact Or.inr ⟨h, h6⟩
  rcases dist_cases H hzc with hd | hd | hd | hd
  · have : ballOpp B t z 4 = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rw [mem_ballOpp] at hx
      have := (H.reach t z).dist_eq_zero_iff.1 hd
      subst this
      omega
    rw [this]; simp
  · have hsub : ballOpp B t z 4 ⊆ X4 B t z := by
      intro x hx
      rcases hcases x hx with h | h | h
      · subst h; have := (mem_ballOpp.1 hx).1; omega
      · have := dist_tri H t z x; omega
      · exact mem_X4.2 h
    have hT := card_T3_le_two H hd
    have h1 := Finset.card_le_card hsub
    have hX2 : (X2 B t z).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rw [mem_X2] at hx
      have := dist_tri H t z x
      omega
    rw [hX2, mul_zero, add_zero] at hid
    have : q * (T3 B t z).card ≤ q * (q * (q * q)) := Nat.mul_le_mul_left q hT
    nlinarith
  · have hsub : ballOpp B t z 4 ⊆ X2 B t z ∪ X4 B t z := by
      intro x hx
      rw [Finset.mem_union]
      rcases hcases x hx with h | h | h
      · subst h; have := (mem_ballOpp.1 hx).1; omega
      · exact Or.inl (mem_X2.2 h)
      · exact Or.inr (mem_X4.2 h)
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint disjoint_X2_X4] at h1
    have hX := X2_ge_four H hzc hd
    have hT := T3_le_four H hd
    -- `|X4| = q |T3| - q |X2|`
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have hT' := Nat.mul_le_mul_left (q' + 1) hT
    nlinarith [Nat.mul_le_mul_left q' hX]
  · have hsub : ballOpp B t z 4 ⊆ insert z (X2 B t z ∪ X4 B t z) := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_union]
      rcases hcases x hx with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (mem_X2.2 h))
      · exact Or.inr (Or.inr (mem_X4.2 h))
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le z (X2 B t z ∪ X4 B t z)
    rw [Finset.card_union_of_disjoint disjoint_X2_X4] at h2
    have hX := X2_ge_six H hq hzc hd
    have hT := T3_le_six H hd
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have hT' := Nat.mul_le_mul_left (q' + 1) hT
    nlinarith [Nat.mul_le_mul_left q' hX]

end BipartiteDD.LeanMaxx.Omega45
