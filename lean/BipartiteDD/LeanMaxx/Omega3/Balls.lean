import BipartiteDD.LeanMaxx.Omega2.Sphere

/-!
# Lemma 3.1 (ball sizes) in a generalized hexagon of order `(q, q)`

`Hex B κ q` bundles what is known about the incidence graph `B` of a generalized hexagon of order `(q, q)`
(proper 2-colouring `κ`, regular of degree `q + 1`, girth 12, diameter 6). Fix a vertex `t` and write
`opp t = sph B t 6` for the vertices opposite `t`. For a centre `z` of the colour of `t` we prove

* `card_ballOpp_two_le`:  `|{x ∈ opp t : dist z x ≤ 2}| ≤ q²`,
* `card_ballOpp_four_le`: `|{x ∈ opp t : dist z x ≤ 4}| ≤ q⁴ + 2 q²`.

(The exact values are `q²` and `q⁴`; only these upper bounds are needed for Theorem 3.3.)
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace BipartiteDD.LeanMaxx.Omega3

open SimpleGraph Finset BipartiteDD.LeanMaxx.Omega2

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The incidence graph of a generalized hexagon of order `(q, q)`, as used in this file. -/
structure Hex (B : SimpleGraph β) [DecidableRel B.Adj] (κ : β → ZMod 2) (q : ℕ) : Prop where
  col : ∀ u v, B.Adj u v → κ u ≠ κ v
  deg : ∀ v, B.degree v = q + 1
  girth : B.egirth = ((2 * 6 : ℕ) : ℕ∞)
  reach : ∀ u v : β, B.Reachable u v
  diam : ∀ u v : β, B.dist u v ≤ 6

variable {B : SimpleGraph β} [DecidableRel B.Adj] {κ : β → ZMod 2} {q : ℕ}

/-- The vertices opposite `t`. -/
noncomputable abbrev opp (B : SimpleGraph β) (t : β) : Finset β := sph B t 6

theorem mem_opp {t x : β} : x ∈ opp B t ↔ B.dist t x = 6 := mem_sph

/-- Distance parity in terms of colours. -/
theorem dist_cast (H : Hex B κ q) (u v : β) : (B.dist u v : ZMod 2) = κ v - κ u := by
  have := col_dist H.col (H.reach u v)
  rw [this]; ring

theorem dist_even_of_col (H : Hex B κ q) {u v : β} (h : κ u = κ v) : Even (B.dist u v) := by
  have := dist_cast H u v
  rw [h, sub_self] at this
  exact (ZMod.natCast_eq_zero_iff_even).1 this

theorem dist_odd_of_col (H : Hex B κ q) {u v : β} (h : κ u ≠ κ v) : Odd (B.dist u v) := by
  have := dist_cast H u v
  have h2 : κ v - κ u = 1 := by
    have := zmod2_eq_add_one h
    rw [this]; ring
  rw [h2] at this
  exact (ZMod.natCast_eq_one_iff_odd).1 this

/-! ### Neighbours of a vertex relative to `t` -/

/-- A neighbour of a vertex opposite `t` is at distance `5` from `t`. -/
theorem dist_five_of_adj_six (H : Hex B κ q) {t x y : β} (hx : B.dist t x = 6) (h : B.Adj x y) :
    B.dist t y = 5 := by
  have := nbr_dist H.col H.reach (u := t) h
  have h6 := H.diam t y
  omega

/-- A vertex at distance `5` from `t` has exactly `q` neighbours opposite `t`. -/
theorem card_opp_nbrs (H : Hex B κ q) {t y : β} (hy : B.dist t y = 5) :
    ((B.neighborFinset y).filter fun x => B.dist t x = 6).card = q :=
  above_card H.col H.deg H.girth H.reach (u := t) (e := 4) (by omega) hy

/-- A vertex at distance `d + 1 ≤ 5` from `t` has exactly one neighbour at distance `d`. -/
theorem card_pred_nbrs (H : Hex B κ q) {t y : β} {d : ℕ} (hd : d ≤ 4) (hy : B.dist t y = d + 1) :
    ((B.neighborFinset y).filter fun x => B.dist t x = d).card = 1 :=
  below_card H.col H.girth H.reach hd hy

theorem card_sph_two (H : Hex B κ q) (u : β) : (sph B u 2).card = q * (q + 1) := by
  have := card_sph_succ H.col H.deg H.girth H.reach (u := u) (e := 0) (by omega)
  simp only [zero_add] at this
  rw [this, card_sph_one H.deg]

theorem card_sph_three (H : Hex B κ q) (u : β) : (sph B u 3).card = q * (q * (q + 1)) := by
  have := card_sph_succ H.col H.deg H.girth H.reach (u := u) (e := 1) (by omega)
  simp only [Nat.reduceAdd] at this
  rw [this, card_sph_two H]


/-! ### The layers around a centre `z` -/

section Layers

variable (B) (t z : β)

/-- Vertices at distance `2` from `z` and opposite `t`. -/
noncomputable def X2 : Finset β := (sph B z 2).filter fun x => B.dist t x = 6
/-- Vertices at distance `4` from `z` and opposite `t`. -/
noncomputable def X4 : Finset β := (sph B z 4).filter fun x => B.dist t x = 6
/-- Vertices at distance `3` from `z` and at distance `5` from `t`. -/
noncomputable def T3 : Finset β := (sph B z 3).filter fun y => B.dist t y = 5

variable {B t z}

theorem mem_X2 {x : β} : x ∈ X2 B t z ↔ B.dist z x = 2 ∧ B.dist t x = 6 := by
  simp [X2, mem_sph]

theorem mem_X4 {x : β} : x ∈ X4 B t z ↔ B.dist z x = 4 ∧ B.dist t x = 6 := by
  simp [X4, mem_sph]

theorem mem_T3 {y : β} : y ∈ T3 B t z ↔ B.dist z y = 3 ∧ B.dist t y = 5 := by
  simp [T3, mem_sph]

theorem disjoint_X2_X4 : Disjoint (X2 B t z) (X4 B t z) := by
  rw [Finset.disjoint_left]
  intro x h2 h4
  rw [mem_X2] at h2; rw [mem_X4] at h4
  omega

/-- The key double count: the vertices at distance `3` from `z` and `5` from `t` each have `q` opposite
neighbours; a vertex of `X2` is the neighbour of `q` of them, a vertex of `X4` of exactly one. -/
theorem X4_add (H : Hex B κ q) : (X4 B t z).card + q * (X2 B t z).card = q * (T3 B t z).card := by
  have key := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := T3 B t z)
    (t := X2 B t z ∪ X4 B t z) B.Adj
  rw [Finset.sum_union disjoint_X2_X4] at key
  have hL : ∑ y ∈ T3 B t z, ((X2 B t z ∪ X4 B t z).bipartiteAbove B.Adj y).card = (T3 B t z).card * q := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [mem_T3] at hy
    have : (X2 B t z ∪ X4 B t z).bipartiteAbove B.Adj y =
        (B.neighborFinset y).filter fun x => B.dist t x = 6 := by
      ext x
      simp only [Finset.bipartiteAbove, Finset.mem_filter, Finset.mem_union, mem_X2, mem_X4,
        mem_neighborFinset]
      constructor
      · rintro ⟨hm, h1⟩
        exact ⟨h1, by rcases hm with h | h <;> exact h.2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h1⟩
        have := nbr_dist H.col H.reach (u := z) h1
        omega
    rw [this]
    exact card_opp_nbrs H hy.2
  have hR2 : ∑ x ∈ X2 B t z, ((T3 B t z).bipartiteBelow B.Adj x).card = (X2 B t z).card * q := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mem_X2] at hx
    have : (T3 B t z).bipartiteBelow B.Adj x =
        (B.neighborFinset x).filter fun y => B.dist z y = 1 + 2 := by
      ext y
      simp only [Finset.bipartiteBelow, Finset.mem_filter, mem_T3, mem_neighborFinset]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h2.symm, by omega⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨by omega, dist_five_of_adj_six H hx.2 h1⟩, h1.symm⟩
    rw [this]
    exact above_card H.col H.deg H.girth H.reach (u := z) (e := 1) (by omega) (by omega)
  have hR4 : ∑ x ∈ X4 B t z, ((T3 B t z).bipartiteBelow B.Adj x).card = (X4 B t z).card := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mem_X4] at hx
    have : (T3 B t z).bipartiteBelow B.Adj x =
        (B.neighborFinset x).filter fun y => B.dist z y = 3 := by
      ext y
      simp only [Finset.bipartiteBelow, Finset.mem_filter, mem_T3, mem_neighborFinset]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h2.symm, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h2, dist_five_of_adj_six H hx.2 h1⟩, h1.symm⟩
    rw [this]
    exact card_pred_nbrs H (t := z) (d := 3) (by omega) (by omega)
  rw [hL, hR2, hR4] at key
  linarith


theorem zmod2_add_one_add_one (a : ZMod 2) : a + 1 + 1 = a := by
  revert a; decide

theorem dist_tri (H : Hex B κ q) (a b c : β) : B.dist a c ≤ B.dist a b + B.dist b c := by
  have : Nonempty β := ⟨a⟩
  have hc : B.Connected := ⟨H.reach⟩
  exact hc.dist_triangle

theorem col_eq_of_dist_even (H : Hex B κ q) {u v : β} (h : Even (B.dist u v)) : κ u = κ v := by
  have := dist_cast H u v
  rw [(ZMod.natCast_eq_zero_iff_even).2 h] at this
  exact (sub_eq_zero.1 this.symm).symm

theorem col_opp (H : Hex B κ q) {t x : β} (h : B.dist t x = 6) : κ t = κ x :=
  col_eq_of_dist_even H (by rw [h]; decide)

/-- Two neighbours of one vertex, of equal colour, are at distance `2` unless equal. -/
theorem dist_two_of_nbrs (H : Hex B κ q) {z u x : β} (h1 : B.Adj z u) (h2 : B.Adj u x) (hne : x ≠ z)
    (hc : κ z = κ x) : B.dist z x = 2 := by
  have hle : B.dist z x ≤ 2 := by
    have := dist_tri H z u x
    have e1 : B.dist z u = 1 := dist_eq_one_iff_adj.mpr h1
    have e2 : B.dist u x = 1 := dist_eq_one_iff_adj.mpr h2
    omega
  have h0 : B.dist z x ≠ 0 := fun h0 => hne ((H.reach z x).dist_eq_zero_iff.1 h0).symm
  have h1' : B.dist z x ≠ 1 := fun h' => H.col z x (dist_eq_one_iff_adj.1 h') hc
  omega

/-- If `z` is at distance `4` or `6` from `t`, at least `q` neighbours of `z` are at distance `5` from `t`. -/
theorem card_nbrs_five (H : Hex B κ q) (hz : B.dist t z = 4 ∨ B.dist t z = 6) :
    q ≤ ((B.neighborFinset z).filter fun u => B.dist t u = 5).card := by
  rcases hz with hz | hz
  · have := above_card H.col H.deg H.girth H.reach (u := t) (e := 3) (by omega) (v := z) (by omega)
    simp only [Nat.reduceAdd] at this
    exact this.ge
  · have h : (B.neighborFinset z).filter (fun u => B.dist t u = 5) = B.neighborFinset z := by
      apply Finset.filter_true_of_mem
      intro u hu
      rw [mem_neighborFinset] at hu
      exact dist_five_of_adj_six H hz hu
    rw [h, card_neighborFinset_eq_degree, H.deg]; omega

/-- For `dist t z ∈ {4, 6}`, `|X2| ≥ q (q - 1)`: every neighbour of `z` at distance `5` from `t` has
`q - 1` neighbours other than `z` opposite `t`, and they lie at distance `2` from `z`. -/
theorem card_X2_ge (H : Hex B κ q) (hq : 1 ≤ q) (hzc : κ z = κ t)
    (hz : B.dist t z = 4 ∨ B.dist t z = 6) : q * q ≤ (X2 B t z).card + q := by
  set U := (B.neighborFinset z).filter fun u => B.dist t u = 5 with hU
  have h1 : U.card * (q - 1) ≤ (X2 B t z).card * 1 := by
    refine Finset.card_mul_le_card_mul B.Adj (s := U) (t := X2 B t z) ?_ ?_
    · intro u hu
      rw [hU, Finset.mem_filter, mem_neighborFinset] at hu
      have hcard := card_opp_nbrs H hu.2
      have hsub : ((B.neighborFinset u).filter fun x => B.dist t x = 6).erase z ⊆
          (X2 B t z).bipartiteAbove B.Adj u := by
        intro x hx
        rw [Finset.mem_erase, Finset.mem_filter, mem_neighborFinset] at hx
        rw [Finset.bipartiteAbove, Finset.mem_filter, mem_X2]
        refine ⟨⟨?_, hx.2.2⟩, hx.2.1⟩
        exact dist_two_of_nbrs H hu.1 hx.2.1 hx.1 (hzc.trans (col_opp H hx.2.2))
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
        rw [Finset.bipartiteBelow, Finset.mem_filter, hU, Finset.mem_filter, mem_neighborFinset] at hu
        rw [Finset.mem_filter, mem_neighborFinset]
        exact ⟨hu.2.symm, dist_eq_one_iff_adj.2 hu.1.1⟩
      have := Finset.card_le_card hsub
      have h3 := card_pred_nbrs H (t := z) (d := 1) (by omega) (y := x) (by omega)
      omega
  have h2 := card_nbrs_five H hz
  have h3 : q * (q - 1) ≤ (X2 B t z).card := by
    calc q * (q - 1) ≤ U.card * (q - 1) := Nat.mul_le_mul_right _ h2
      _ ≤ (X2 B t z).card := by simpa using h1
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h3
  nlinarith


/-- If `z` is at distance `2` from `t`, then `|T3| ≤ q³`: the `q²` vertices at distance `2` from the middle
vertex `m` (other than those through `z`) are at distance `3` from `z` and at most `3` from `t`. -/
theorem card_T3_le_two (H : Hex B κ q) (hz : B.dist t z = 2) : (T3 B t z).card ≤ q * (q * q) := by
  obtain ⟨m, hzm, hm⟩ := exists_pred H.reach (u := t) (v := z) (e := 1) (by omega)
  set W := (sph B m 2).filter fun y => ¬ B.Adj z y with hW
  have hmz : κ m ≠ κ z := H.col m z hzm.symm
  have hcardW : W.card = q * q := by
    have h1 := Finset.card_filter_add_card_filter_not (s := sph B m 2) (fun y => B.Adj z y)
    have h2 : (sph B m 2).filter (fun y => B.Adj z y) = (B.neighborFinset z).erase m := by
      ext y
      simp only [Finset.mem_filter, mem_sph, Finset.mem_erase, mem_neighborFinset]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        intro hym
        rw [hym, dist_self] at h1
        omega
      · rintro ⟨h1, h2⟩
        refine ⟨dist_two_of_nbrs H hzm.symm h2 h1 ?_, h2⟩
        have e1 := zmod2_eq_add_one (H.col z y h2)
        have e2 := zmod2_eq_add_one hmz
        rw [e1, e2]; exact (zmod2_add_one_add_one _).symm
    rw [h2, Finset.card_erase_of_mem ((mem_neighborFinset B z m).2 hzm), card_neighborFinset_eq_degree,
      H.deg, card_sph_two H] at h1
    simp only [W]
    rw [Nat.add_sub_cancel] at h1
    nlinarith
  have hdisj : Disjoint (T3 B t z) W := by
    rw [Finset.disjoint_left]
    intro y hT hWy
    rw [mem_T3] at hT
    simp only [W, Finset.mem_filter, mem_sph] at hWy
    have := dist_tri H t m y
    rw [hm] at this
    omega
  have hsub : T3 B t z ∪ W ⊆ sph B z 3 := by
    intro y hy
    rw [Finset.mem_union] at hy
    rcases hy with hy | hy
    · exact (Finset.mem_filter.1 hy).1
    · simp only [W, Finset.mem_filter, mem_sph] at hy
      rw [mem_sph]
      have hle : B.dist z y ≤ 3 := by
        have := dist_tri H z m y
        have e1 : B.dist z m = 1 := dist_eq_one_iff_adj.mpr hzm
        omega
      have hcol : κ z ≠ κ y := by
        have := col_eq_of_dist_even H (u := m) (v := y) (by rw [hy.1]; decide)
        rw [← this]; exact hmz.symm
      have hodd := dist_odd_of_col H hcol
      have h1 : B.dist z y ≠ 1 := fun h' => hy.2 (dist_eq_one_iff_adj.1 h')
      obtain ⟨k, hk⟩ := hodd
      omega
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, card_sph_three H, hcardW] at this
  nlinarith


/-- The vertices opposite `t` within distance `r` of `z`. -/
noncomputable def ballOpp (B : SimpleGraph β) (t z : β) (r : ℕ) : Finset β :=
  (opp B t).filter fun x => B.dist z x ≤ r

theorem mem_ballOpp {r : ℕ} {x : β} : x ∈ ballOpp B t z r ↔ B.dist t x = 6 ∧ B.dist z x ≤ r := by
  simp [ballOpp, mem_opp]

theorem ballOpp_mono {r r' : ℕ} (h : r ≤ r') : ballOpp B t z r ⊆ ballOpp B t z r' := by
  intro x hx
  rw [mem_ballOpp] at hx ⊢
  exact ⟨hx.1, hx.2.trans h⟩

theorem col_eq_of_adj_adj (H : Hex B κ q) {a b c : β} (h1 : B.Adj a b) (h2 : B.Adj b c) : κ a = κ c := by
  have e1 := zmod2_eq_add_one (H.col a b h1)
  have e2 := zmod2_eq_add_one (H.col b c h2)
  rw [e2, e1, zmod2_add_one_add_one]

theorem ballOpp_even (H : Hex B κ q) (hzc : κ z = κ t) {r : ℕ} {x : β} (hx : x ∈ ballOpp B t z r) :
    Even (B.dist z x) := by
  rw [mem_ballOpp] at hx
  exact dist_even_of_col H (hzc.trans (col_opp H hx.1))

/-- A centre of the colour of `t` is at distance `0, 2, 4` or `6` from `t`. -/
theorem dist_cases (H : Hex B κ q) (hzc : κ z = κ t) :
    B.dist t z = 0 ∨ B.dist t z = 2 ∨ B.dist t z = 4 ∨ B.dist t z = 6 := by
  obtain ⟨k, hk⟩ := dist_even_of_col H hzc.symm
  have h6 := H.diam t z
  omega


/-- At most `q²` vertices opposite `t` lie within distance `2` of a centre of the colour of `t`. -/
theorem card_ballOpp_two_le (H : Hex B κ q) (hq : 1 ≤ q) (hzc : κ z = κ t) :
    (ballOpp B t z 2).card ≤ q ^ 2 := by
  -- a vertex at distance `2` from `z` opposite `t` is not near `t`
  have hS2 : (X2 B t z).card + ((sph B z 2).filter fun x => B.dist t x ≠ 6).card = q * (q + 1) := by
    have := Finset.card_filter_add_card_filter_not (s := sph B z 2) (fun x => B.dist t x = 6)
    rw [card_sph_two H] at this
    exact this
  rcases dist_cases H hzc with hd | hd | hd | hd
  · -- z = t
    have : ballOpp B t z 2 = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rw [mem_ballOpp] at hx
      have := dist_tri H t z x
      omega
    rw [this]; simp
  · have : ballOpp B t z 2 = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rw [mem_ballOpp] at hx
      have := dist_tri H t z x
      omega
    rw [this]; simp
  · -- `dist t z = 4`: `z` has a neighbour `b` at distance `3`; its other `q` neighbours are near `t`
    obtain ⟨b, hzb, hb⟩ := exists_pred H.reach (u := t) (v := z) (e := 3) (by omega)
    have hY : ((B.neighborFinset b).erase z) ⊆ (sph B z 2).filter fun x => B.dist t x ≠ 6 := by
      intro x hx
      rw [Finset.mem_erase, mem_neighborFinset] at hx
      rw [Finset.mem_filter, mem_sph]
      refine ⟨dist_two_of_nbrs H hzb hx.2 hx.1 (col_eq_of_adj_adj H hzb hx.2), ?_⟩
      · have := dist_tri H t b x
        have e1 : B.dist b x = 1 := dist_eq_one_iff_adj.mpr hx.2
        omega
    have hq' : q ≤ ((sph B z 2).filter fun x => B.dist t x ≠ 6).card := by
      have := Finset.card_le_card hY
      rw [Finset.card_erase_of_mem ((mem_neighborFinset B b z).2 hzb.symm), card_neighborFinset_eq_degree,
        H.deg] at this
      omega
    have hsub : ballOpp B t z 2 ⊆ X2 B t z := by
      intro x hx
      rw [mem_ballOpp] at hx
      rw [mem_X2]
      refine ⟨?_, hx.1⟩
      have he := ballOpp_even H hzc (Finset.mem_of_subset (ballOpp_mono (le_refl 2)) (mem_ballOpp.2 hx))
      obtain ⟨k, hk⟩ := he
      have h0 : B.dist z x ≠ 0 := by
        intro h0
        have := (H.reach z x).dist_eq_zero_iff.1 h0
        subst this
        omega
      omega
    have := Finset.card_le_card hsub
    nlinarith
  · -- `dist t z = 6`: the `q + 1` neighbours of `z` each have a neighbour at distance `4` from `t`
    set Z := (sph B z 2).filter fun x => B.dist t x = 4 with hZ
    have hZsub : Z ⊆ (sph B z 2).filter fun x => B.dist t x ≠ 6 := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, by omega⟩
    have hq' : q + 1 ≤ Z.card := by
      have h := Finset.card_mul_le_card_mul B.Adj (s := B.neighborFinset z) (t := Z) (m := 1) (n := 1) ?_ ?_
      · rw [card_neighborFinset_eq_degree, H.deg] at h; omega
      · intro u hu
        rw [mem_neighborFinset] at hu
        have h5 := dist_five_of_adj_six H hd hu
        have hc := card_pred_nbrs H (t := t) (d := 4) (by omega) h5
        obtain ⟨x, hx⟩ := Finset.card_pos.1 (by omega : 0 < ((B.neighborFinset u).filter fun x => B.dist t x = 4).card)
        rw [Finset.mem_filter, mem_neighborFinset] at hx
        have : x ∈ Z.bipartiteAbove B.Adj u := by
          rw [Finset.bipartiteAbove, Finset.mem_filter, hZ, Finset.mem_filter, mem_sph]
          refine ⟨⟨?_, hx.2⟩, hx.1⟩
          refine dist_two_of_nbrs H hu hx.1 ?_ ?_
          · rintro rfl; omega
          · exact (col_eq_of_adj_adj H hu hx.1)
        exact Finset.card_pos.2 ⟨x, this⟩
      · intro x hx
        rw [hZ, Finset.mem_filter, mem_sph] at hx
        have hsub : (B.neighborFinset z).bipartiteBelow B.Adj x ⊆ (B.neighborFinset x).filter fun y => B.dist z y = 1 := by
          intro u hu
          rw [Finset.bipartiteBelow, Finset.mem_filter, mem_neighborFinset] at hu
          rw [Finset.mem_filter, mem_neighborFinset]
          exact ⟨hu.2.symm, dist_eq_one_iff_adj.2 hu.1⟩
        have := Finset.card_le_card hsub
        have h3 := card_pred_nbrs H (t := z) (d := 1) (by omega) (y := x) (by omega)
        omega
    have hsub : ballOpp B t z 2 ⊆ insert z (X2 B t z) := by
      intro x hx
      rw [Finset.mem_insert]
      by_cases hxz : x = z
      · exact Or.inl hxz
      · right
        rw [mem_X2]
        refine ⟨?_, (mem_ballOpp.1 hx).1⟩
        have he := ballOpp_even H hzc hx
        have hle := (mem_ballOpp.1 hx).2
        obtain ⟨k, hk⟩ := he
        have h0 : B.dist z x ≠ 0 := fun h0 => hxz ((H.reach z x).dist_eq_zero_iff.1 h0).symm
        omega
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le z (X2 B t z)
    have h3 := Finset.card_le_card hZsub
    nlinarith


/-- At most `q⁴ + 2q²` vertices opposite `t` lie within distance `4` of a centre of the colour of `t`
(the exact value is `q⁴`). -/
theorem card_ballOpp_four_le (H : Hex B κ q) (hq : 1 ≤ q) (hzc : κ z = κ t) :
    (ballOpp B t z 4).card ≤ q ^ 4 + 2 * q ^ 2 := by
  have hid := X4_add (B := B) (t := t) (z := z) H
  have hT3 : (T3 B t z).card ≤ q * (q * (q + 1)) := by
    have : T3 B t z ⊆ sph B z 3 := fun y hy => (Finset.mem_filter.1 hy).1
    have := Finset.card_le_card this
    rwa [card_sph_three H] at this
  -- every vertex of the ball is `z` itself or lies in `X2 ∪ X4`
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
  · -- z = t
    have : ballOpp B t z 4 = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rw [mem_ballOpp] at hx
      have := (H.reach t z).dist_eq_zero_iff.1 hd
      subst this
      omega
    rw [this]; simp
  · -- `dist t z = 2`: the ball lies in `X4`, and `T3` is small
    have hsub : ballOpp B t z 4 ⊆ X4 B t z := by
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
  · -- `dist t z = 4`
    have hsub : ballOpp B t z 4 ⊆ X2 B t z ∪ X4 B t z := by
      intro x hx
      rw [Finset.mem_union]
      rcases hcases x hx with h | h | h
      · subst h; have := (mem_ballOpp.1 hx).1; omega
      · exact Or.inl (mem_X2.2 h)
      · exact Or.inr (mem_X4.2 h)
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint disjoint_X2_X4] at h1
    have hX := card_X2_ge H hq hzc (Or.inl hd)
    have : q * (T3 B t z).card ≤ q * (q * (q * (q + 1))) := Nat.mul_le_mul_left q hT3
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    nlinarith [Nat.mul_le_mul_left q' hX]
  · -- `dist t z = 6`
    have hsub : ballOpp B t z 4 ⊆ insert z (X2 B t z ∪ X4 B t z) := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_union]
      rcases hcases x hx with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (mem_X2.2 h))
      · exact Or.inr (Or.inr (mem_X4.2 h))
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le z (X2 B t z ∪ X4 B t z)
    rw [Finset.card_union_of_disjoint disjoint_X2_X4] at h2
    have hX := card_X2_ge H hq hzc (Or.inr hd)
    have : q * (T3 B t z).card ≤ q * (q * (q * (q + 1))) := Nat.mul_le_mul_left q hT3
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    nlinarith [Nat.mul_le_mul_left q' hX]

end Layers

end BipartiteDD.LeanMaxx.Omega3
