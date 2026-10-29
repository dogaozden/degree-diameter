import BipartiteDD.LeanMaxx.Omega45b.Bonf
import BipartiteDD.LeanMaxx.Omega45b.Bridge
import BipartiteDD.LeanMaxx.Omega45b.Points
import BipartiteDD.LeanMaxx.Omega45b.QuadCount
import BipartiteDD.LeanMaxx.Omega45.Q7
import BipartiteDD.LeanMaxx.Omega45.Exact

/-!
# Lemma 4.3 for `H(7)`: the statement `Bonferroni` of `Omega45/Q7.lean` for the actual hexagon

`bonferroni_H7`: for the incidence graph `G7` of `H(7)` (a generalized hexagon of order `(7,7)`), points
`t, y₁, …, y₅` (pairwise distinct) with fewer than four of the fifteen pairs at distance `≤ 4` satisfy
`|⋃ {x : dist t x = 6, dist yᵢ x ≤ 4}| + 140 · 49 < 7⁵`.

Proof: `bonf3` and `union_bound` (`Bonf.lean`, Bonferroni with the overlaps `≥ 336` of pairs and `≤ 64` of triples)
with the quadric counts of `QuadCount.lean` (Lemma 4.1) transported to points (`Points.lean`) and to the graph
(`Bridge.lean`: distance `≤ 4` between points is perpendicularity).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace BipartiteDD.LeanMaxx.Omega45b

open BipartiteDD.Hexagon BipartiteDD.LeanMaxx.Omega2 BipartiteDD.LeanMaxx.Omega3 BipartiteDD.LeanMaxx.Omega45 Finset

theorem indep_pair_of_ne {x y : SPt F7} (hxy : x ≠ y) : LinearIndependent F7 ![x.1.rep, y.1.rep] := by
  rw [LinearIndependent.pair_iff]
  intro a b h
  exact lin_indep_pair hxy h

theorem Bf_smul_right (c : F7) (u v : V7 F7) : Bf u (c • v) = c * Bf u v := by
  simp only [Bf, Pi.smul_apply, smul_eq_mul]; ring

/-! ### Counting points -/

/-- Pair overlaps (Lemma 4.1): at least `336` singular points are perpendicular to `y, y'` and not to `t`. -/
theorem pair_overlap_pts {t y y' : SPt F7} (hli : LinearIndependent F7 ![y.1.rep, y'.1.rep, t.1.rep]) :
    336 ≤ (Finset.univ.filter fun x : SPt F7 =>
      Bf t.1.rep x.1.rep ≠ 0 ∧ Bf y.1.rep x.1.rep = 0 ∧ Bf y'.1.rep x.1.rep = 0).card := by
  classical
  have h6 := card_pts_mul (fun v : V7 F7 => Bf t.1.rep v ≠ 0 ∧ Bf y.1.rep v = 0 ∧ Bf y'.1.rep v = 0)
    (fun c v hc => by
      simp only [Bf_smul_right]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨fun h => h1 (by rw [h, mul_zero]), (mul_eq_zero.1 h2).resolve_left hc,
          (mul_eq_zero.1 h3).resolve_left hc⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨mul_ne_zero hc h1, by rw [h2, mul_zero], by rw [h3, mul_zero]⟩)
  have hyy : LinearIndependent F7 ![y.1.rep, y'.1.rep] := by
    have h := hli.comp (![0, 1] : Fin 2 → Fin 3) (by decide)
    convert h using 1
    ext i; fin_cases i <;> rfl
  have h2 := card_perpZeros_two y.2 y'.2 hyy
  have h3 := card_perpZeros_three_le y.2 y'.2 t.2 hli
  have hsub : perpZeros [y.1.rep, y'.1.rep, t.1.rep] ⊆ perpZeros [y.1.rep, y'.1.rep] := by
    intro x hx
    simp only [perpZeros, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons, forall_eq_or_imp,
      List.not_mem_nil, or_false, forall_eq] at hx ⊢
    exact ⟨hx.1, hx.2.1, hx.2.2.1⟩
  have hsub2 : perpZeros [y.1.rep, y'.1.rep] \ perpZeros [y.1.rep, y'.1.rep, t.1.rep] ⊆
      Finset.univ.filter fun v : V7 F7 =>
        v ≠ 0 ∧ Qf v = 0 ∧ (Bf t.1.rep v ≠ 0 ∧ Bf y.1.rep v = 0 ∧ Bf y'.1.rep v = 0) := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hx1, hx2⟩ := hx
    simp only [perpZeros, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons, forall_eq_or_imp,
      List.not_mem_nil, or_false, forall_eq, not_and] at hx1 hx2 ⊢
    have hbt : Bf x t.1.rep ≠ 0 := fun h => hx2 hx1.1 hx1.2.1 hx1.2.2 h
    rw [Bf_comm] at hbt
    refine ⟨fun h => hbt (by rw [h]; simp [Bf]), hx1.1, hbt, ?_, ?_⟩
    · rw [Bf_comm]; exact hx1.2.1
    · rw [Bf_comm]; exact hx1.2.2
  have := Finset.card_le_card hsub2
  rw [Finset.card_sdiff_of_subset hsub] at this
  omega

/-- Triple overlaps (Lemma 4.1): at most `64` singular points are perpendicular to three independent
singular points. -/
theorem triple_pts_le {x y z : SPt F7}
    (hli : LinearIndependent F7 ![x.1.rep, y.1.rep, z.1.rep]) :
    (Finset.univ.filter fun p : SPt F7 =>
      Bf x.1.rep p.1.rep = 0 ∧ Bf y.1.rep p.1.rep = 0 ∧ Bf z.1.rep p.1.rep = 0).card ≤ 64 := by
  classical
  have h6 := card_pts_mul (fun v : V7 F7 => Bf x.1.rep v = 0 ∧ Bf y.1.rep v = 0 ∧ Bf z.1.rep v = 0)
    (fun c v hc => by
      simp only [Bf_smul_right]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨(mul_eq_zero.1 h1).resolve_left hc, (mul_eq_zero.1 h2).resolve_left hc,
          (mul_eq_zero.1 h3).resolve_left hc⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨by rw [h1, mul_zero], by rw [h2, mul_zero], by rw [h3, mul_zero]⟩)
  have h3 := card_perpZeros_three_le x.2 y.2 z.2 hli
  have hsub : (Finset.univ.filter fun v : V7 F7 =>
      v ≠ 0 ∧ Qf v = 0 ∧ (Bf x.1.rep v = 0 ∧ Bf y.1.rep v = 0 ∧ Bf z.1.rep v = 0)) ⊆
      (perpZeros [x.1.rep, y.1.rep, z.1.rep]).erase 0 := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rw [Finset.mem_erase]
    refine ⟨hv.1, ?_⟩
    simp only [perpZeros, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons, forall_eq_or_imp,
      List.not_mem_nil, or_false, forall_eq]
    refine ⟨hv.2.1, ?_, ?_, ?_⟩
    · rw [Bf_comm]; exact hv.2.2.1
    · rw [Bf_comm]; exact hv.2.2.2.1
    · rw [Bf_comm]; exact hv.2.2.2.2
  have h0 : (0 : V7 F7) ∈ perpZeros [x.1.rep, y.1.rep, z.1.rep] := by
    simp [perpZeros, Qf, Bf]
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem h0] at this
  omega

/-! ### The balls in the graph -/

theorem sum_off (cl : Fin 5 → Fin 5 → Bool) (hsym : ∀ i j, cl i j = cl j i) :
    (∑ i : Fin 5, ∑ j : Fin 5, (if i ≠ j ∧ cl i j = true then 1 else 0 : ℕ)) =
      2 * ((cl 0 1).toNat + (cl 0 2).toNat + (cl 0 3).toNat + (cl 0 4).toNat + (cl 1 2).toNat +
        (cl 1 3).toNat + (cl 1 4).toNat + (cl 2 3).toNat + (cl 2 4).toNat + (cl 3 4).toNat) := by
  simp only [Fin.sum_univ_five]
  have h10 := hsym 1 0; have h20 := hsym 2 0; have h30 := hsym 3 0; have h40 := hsym 4 0
  have h21 := hsym 2 1; have h31 := hsym 3 1; have h41 := hsym 4 1
  have h32 := hsym 3 2; have h42 := hsym 4 2; have h43 := hsym 4 3
  simp only [h10, h20, h30, h40, h21, h31, h41, h32, h42, h43]
  simp only [ne_eq, not_true_eq_false, false_and, ite_false, zero_add, add_zero]
  generalize cl 0 1 = a01; generalize cl 0 2 = a02; generalize cl 0 3 = a03; generalize cl 0 4 = a04
  generalize cl 1 2 = a12; generalize cl 1 3 = a13; generalize cl 1 4 = a14
  generalize cl 2 3 = a23; generalize cl 2 4 = a24; generalize cl 3 4 = a34
  revert a01 a02 a03 a04 a12 a13 a14 a23 a24 a34
  decide

section Graph

variable [Fintype (SPt F7 ⊕ HLine F7)] [DecidableEq (SPt F7 ⊕ HLine F7)] [DecidableRel G7.Adj]

/-- Membership in the radius-4 ball of a point opposite a point `t`, in terms of the quadric. -/
theorem mem_ballOpp_inl (H : Hex G7 klass 7) (t y : SPt F7) (x : SPt F7 ⊕ HLine F7) :
    x ∈ ballOpp G7 (Sum.inl t) (Sum.inl y) 4 ↔
      ∃ p : SPt F7, x = Sum.inl p ∧ Bf t.1.rep p.1.rep ≠ 0 ∧ Bf y.1.rep p.1.rep = 0 := by
  rw [mem_ballOpp]
  constructor
  · rintro ⟨h6, h4⟩
    rcases x with p | l
    · exact ⟨p, rfl, (dist_inl_eq_six_iff t p).1 h6, (dist_inl_le_four_iff y p).1 h4⟩
    · exfalso
      have := col_opp H h6
      simp [klass] at this
  · rintro ⟨p, rfl, h1, h2⟩
    exact ⟨(dist_inl_eq_six_iff t p).2 h1, (dist_inl_le_four_iff y p).2 h2⟩

/-- A pair of balls overlaps in `≥ 336` vertices when `t, y, y'` span a plane. -/
theorem pair_overlap (H : Hex G7 klass 7) {t y y' : SPt F7}
    (hli : LinearIndependent F7 ![y.1.rep, y'.1.rep, t.1.rep]) :
    336 ≤ (ballOpp G7 (Sum.inl t) (Sum.inl y) 4 ∩ ballOpp G7 (Sum.inl t) (Sum.inl y') 4).card := by
  refine (pair_overlap_pts hli).trans ?_
  refine Finset.card_le_card_of_injOn (fun p => (Sum.inl p : SPt F7 ⊕ HLine F7)) ?_ ?_
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp
    simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe, mem_ballOpp_inl H]
    exact ⟨⟨p, rfl, hp.1, hp.2.1⟩, ⟨p, rfl, hp.1, hp.2.2⟩⟩
  · intro a _ b _ h
    exact Sum.inl_injective h

theorem triple_overlap (H : Hex G7 klass 7) {t x y z : SPt F7}
    (hli : LinearIndependent F7 ![x.1.rep, y.1.rep, z.1.rep]) :
    (ballOpp G7 (Sum.inl t) (Sum.inl x) 4 ∩ ballOpp G7 (Sum.inl t) (Sum.inl y) 4 ∩
      ballOpp G7 (Sum.inl t) (Sum.inl z) 4).card ≤ 64 := by
  refine le_trans ?_ (triple_pts_le hli)
  refine Finset.card_le_card_of_injOn (fun v : SPt F7 ⊕ HLine F7 => v.elim id (fun _ => x)) ?_ ?_
  · intro v hv
    simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe, mem_ballOpp_inl H] at hv
    obtain ⟨⟨⟨p, rfl, h1, h2⟩, ⟨p', hp', h3, h4⟩⟩, ⟨p'', hp'', h5, h6⟩⟩ := hv
    have e1 := Sum.inl_injective hp'
    have e2 := Sum.inl_injective hp''
    subst e1 e2
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, Sum.elim_inl, id_eq]
    exact ⟨h2, h4, h6⟩
  · intro a ha b hb h
    simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe, mem_ballOpp_inl H] at ha hb
    obtain ⟨⟨⟨p, rfl, _⟩, _⟩, _⟩ := ha
    obtain ⟨⟨⟨p', rfl, _⟩, _⟩, _⟩ := hb
    simpa using h

/-- **Lemma 4.3 for `H(7)`** (the statement `Bonferroni` of `Omega45/Q7.lean`, with `k = 4`, `m = 140`, for the
colour class of the points). -/
theorem bonferroni_of_hex (H : Hex G7 klass 7) : Bonferroni G7 klass 0 4 140 := by
  intro t Y ht hY5 hY hcl
  obtain ⟨tp, rfl⟩ : ∃ tp, t = Sum.inl tp := by
    rcases t with p | l
    · exact ⟨p, rfl⟩
    · simp [klass] at ht
  have hYp : ∀ y ∈ Y, ∃ p : SPt F7, y = Sum.inl p := by
    intro y hy
    rcases y with p | l
    · exact ⟨p, rfl⟩
    · have := (hY _ hy).1
      simp [klass] at this
  let e : Y ≃ Fin 5 := Finset.equivFinOfCardEq hY5
  choose pp hpp using fun i : Fin 5 => hYp (e.symm i).1 (e.symm i).2
  let g : Fin 5 → SPt F7 ⊕ HLine F7 := fun i => Sum.inl (pp i)
  have hg : ∀ i, g i = (e.symm i).1 := fun i => (hpp i).symm
  have hginj : Function.Injective g := by
    intro i j h
    have : (e.symm i).1 = (e.symm j).1 := by rw [← hg, ← hg, h]
    exact e.symm.injective (Subtype.ext this)
  have hYeq : Y = Finset.univ.image g := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hy
      refine ⟨e ⟨y, hy⟩, ?_⟩
      rw [hg]; simp
    · rintro ⟨i, rfl⟩
      rw [hg]; exact (e.symm i).2
  have hppinj : Function.Injective pp := fun i j h => hginj (by simp [g, h])
  have hne_t : ∀ i, pp i ≠ tp := by
    intro i h
    have := (hY (g i) (by rw [hYeq]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i))).2
    exact this (by simp [g, h])
  -- the five balls
  let c : Fin 5 → Finset (SPt F7 ⊕ HLine F7) := fun i => ballOpp G7 (Sum.inl tp) (Sum.inl (pp i)) 4
  let cT : Fin 5 → Bool := fun i => decide (Bf tp.1.rep (pp i).1.rep = 0)
  let cl : Fin 5 → Fin 5 → Bool := fun i j => decide (Bf (pp i).1.rep (pp j).1.rep = 0)
  have hBfc : ∀ x y : SPt F7, Bf x.1.rep y.1.rep = Bf y.1.rep x.1.rep := fun x y => Bf_comm _ _
  have hsize : ∀ i, (c i).card ≤ 2401 := fun i => by
    have := card_ballOpp_four_le_exact H (q := 7) (t := Sum.inl tp) (z := Sum.inl (pp i)) (by norm_num) rfl
    simpa using this
  have hpair : ∀ i j, i < j → ¬(cT i = true ∧ cT j = true ∧ cl i j = true) → 336 ≤ (c i ∩ c j).card := by
    intro i j hij hn
    have hne : pp i ≠ pp j := fun h => (ne_of_lt hij) (hppinj h)
    refine pair_overlap H ?_
    by_contra hd
    obtain ⟨h1, h2, h3⟩ := perp_of_dependent hne (hne_t i) (hne_t j) hd
    apply hn
    refine ⟨?_, ?_, ?_⟩
    · simp [cT]; rw [hBfc]; exact h2
    · simp [cT]; rw [hBfc]; exact h3
    · simp [cl]; exact h1
  have hsym : ∀ i j, cl i j = cl j i := fun i j => by
    simp only [cl, hBfc (pp i) (pp j)]
  have htri : ∀ i j k, i < j → j < k → ¬(cl i j = true ∧ cl i k = true ∧ cl j k = true) →
      (c i ∩ c j ∩ c k).card ≤ 64 := by
    intro i j k hij hjk hn
    have hne1 : pp i ≠ pp j := fun h => (ne_of_lt hij) (hppinj h)
    have hne2 : pp i ≠ pp k := fun h => (ne_of_lt (hij.trans hjk)) (hppinj h)
    have hne3 : pp j ≠ pp k := fun h => (ne_of_lt hjk) (hppinj h)
    refine triple_overlap H ?_
    by_contra hd
    obtain ⟨h1, h2, h3⟩ := perp_of_dependent hne1 hne2 hne3 hd
    exact hn ⟨by simp [cl]; exact h1, by simp [cl]; exact h2, by simp [cl]; exact h3⟩
  have key : ∀ f : SPt F7 ⊕ HLine F7 → ℕ, ∑ y ∈ Y, f y = ∑ i : Fin 5, f (g i) := by
    intro f
    rw [hYeq, Finset.sum_image (fun a _ b _ h => hginj h)]
  have hA : (Y.filter fun y => G7.dist (Sum.inl tp) y ≤ 4).card = ∑ i : Fin 5, (cT i).toNat := by
    rw [Finset.card_filter, key]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [g, cT, dist_inl_le_four_iff]
    by_cases h : Bf tp.1.rep (pp i).1.rep = 0 <;> simp [h]
  have hBc : ((Y ×ˢ Y).filter fun p => p.1 ≠ p.2 ∧ G7.dist p.1 p.2 ≤ 4).card =
      ∑ i : Fin 5, ∑ j : Fin 5, (if i ≠ j ∧ cl i j = true then 1 else 0 : ℕ) := by
    rw [Finset.card_filter, Finset.sum_product, key]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [key]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [g, cl, dist_inl_le_four_iff, ne_eq, Sum.inl.injEq]
    by_cases h : Bf (pp i).1.rep (pp j).1.rep = 0
    · by_cases hij : pp i = pp j
      · have : i = j := hppinj hij
        simp [this]
      · have : i ≠ j := fun h' => hij (h' ▸ rfl)
        simp [h, hij, this, dist_inl_le_four_iff]
    · simp [h, dist_inl_le_four_iff]
  have hT : (cT 0).toNat + (cT 1).toNat + (cT 2).toNat + (cT 3).toNat + (cT 4).toNat + (cl 0 1).toNat +
      (cl 0 2).toNat + (cl 0 3).toNat + (cl 0 4).toNat + (cl 1 2).toNat + (cl 1 3).toNat + (cl 1 4).toNat +
      (cl 2 3).toNat + (cl 2 4).toNat + (cl 3 4).toNat ≤ 3 := by
    rw [hA, hBc, sum_off cl hsym, Fin.sum_univ_five] at hcl
    omega
  have hU := union_bound c cT cl hsize hpair htri hT
  have hbi : (Y.biUnion fun y => ballOpp G7 (Sum.inl tp) y 4) = c 0 ∪ c 1 ∪ c 2 ∪ c 3 ∪ c 4 := by
    have hall : ∀ i : Fin 5, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by decide
    have hmem : ∀ i : Fin 5, g i ∈ Y := fun i => by
      rw [hYeq]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_union]
    constructor
    · rintro ⟨y, hy, hx⟩
      rw [hYeq, Finset.mem_image] at hy
      obtain ⟨i, _, rfl⟩ := hy
      have hx' : x ∈ c i := hx
      rcases hall i with rfl | rfl | rfl | rfl | rfl <;> tauto
    · intro h
      rcases h with (((h | h) | h) | h) | h
      · exact ⟨g 0, hmem 0, h⟩
      · exact ⟨g 1, hmem 1, h⟩
      · exact ⟨g 2, hmem 2, h⟩
      · exact ⟨g 3, hmem 3, h⟩
      · exact ⟨g 4, hmem 4, h⟩
  rw [hbi]
  omega

end Graph

end BipartiteDD.LeanMaxx.Omega45b
