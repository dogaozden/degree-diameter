import BipartiteDD.SingerC.W3Basic

/-! Corollary C1, step 2 (continued, work in progress): the GQ axioms of W(3,q). -/

namespace BipartiteDD.SingerC

open Module Projectivization
open scoped LinearAlgebra.Projectivization

namespace Setting

variable {K : Type*} [Field K] [Fintype K] {p : ℕ} [Fact p.Prime] [CharP K p]
variable (S : Setting K p)

theorem B_cross_pts (x y : ℙ S.F K) (h : S.B x.rep y.rep = 0) {b : K} (hb : b ∈ y.submodule) :
    S.B x.rep b = 0 := by
  rw [Projectivization.submodule_eq] at hb
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
  show S.B x.rep ((c : K) * y.rep) = 0
  rw [S.B_smul_right _ c.2, h, mul_zero]

theorem one_line (x y : ℙ S.F K) (l m : S.TILine) (hxl : x ∈ l) (hyl : y ∈ l) (hxm : x ∈ m)
    (hym : y ∈ m) : x = y ∨ l = m := by
  by_cases hxy : x = y
  · exact Or.inl hxy
  · right
    have hxl' : x.submodule ≤ l.1 := hxl
    have hyl' : y.submodule ≤ l.1 := hyl
    have hxm' : x.submodule ≤ m.1 := hxm
    have hym' : y.submodule ≤ m.1 := hym
    have hdim := S.finrank_sup_of_ne hxy
    have e1 : x.submodule ⊔ y.submodule = l.1 :=
      Submodule.eq_of_le_of_finrank_eq (sup_le hxl' hyl') (by rw [hdim, l.2.1])
    have e2 : x.submodule ⊔ y.submodule = m.1 :=
      Submodule.eq_of_le_of_finrank_eq (sup_le hxm' hym') (by rw [hdim, m.2.1])
    exact Subtype.ext (e1.symm.trans e2)

/-- The line through two distinct collinear points. -/
def lineOf {x y : ℙ S.F K} (hxy : x ≠ y) (h : S.B x.rep y.rep = 0) : S.TILine :=
  ⟨x.submodule ⊔ y.submodule, S.finrank_sup_of_ne hxy,
    S.B_sup (fun a ha a' ha' => S.B_point x ha ha') (fun b hb b' hb' => S.B_point y hb hb')
      (fun a ha b hb => S.B_cross x ha (S.B_cross_pts x y h hb))⟩

theorem mem_lineOf {x y : ℙ S.F K} (hxy : x ≠ y) (h : S.B x.rep y.rep = 0) :
    x ∈ S.lineOf hxy h ∧ y ∈ S.lineOf hxy h :=
  ⟨le_sup_left, le_sup_right⟩

/-- Two distinct points of a line through `x` span it. -/
theorem lineOf_eq {x y : ℙ S.F K} (hxy : x ≠ y) (h : S.B x.rep y.rep = 0) (l : S.TILine)
    (hxl : x ∈ l) (hyl : y ∈ l) : S.lineOf hxy h = l := by
  have hxl' : x.submodule ≤ l.1 := hxl
  have hyl' : y.submodule ≤ l.1 := hyl
  apply Subtype.ext
  show x.submodule ⊔ y.submodule = l.1
  exact Submodule.eq_of_le_of_finrank_eq (sup_le hxl' hyl')
    (by rw [S.finrank_sup_of_ne hxy, l.2.1])

theorem rep_mem' (x : ℙ S.F K) : x.rep ∈ x.submodule := by
  rw [Projectivization.submodule_eq]
  exact Submodule.mem_span_singleton_self _

theorem finrank_ker_Bfun {v : K} (hv : v ≠ 0) :
    finrank S.F (LinearMap.ker (S.Bfun v)) = 3 := by
  have hrank := LinearMap.finrank_range_add_finrank_ker (S.Bfun v)
  have hrange : LinearMap.range (S.Bfun v) = ⊤ := by
    obtain ⟨y, hy⟩ := S.B_nondeg hv
    rw [LinearMap.range_eq_top]
    intro c
    let t : S.F := ⟨S.B v y, S.B_mem_F v y⟩
    have ht : t ≠ 0 := fun h => hy (congrArg Subtype.val h)
    refine LinearMap.mem_range.mpr ⟨(c / t : S.F) • y, Subtype.ext ?_⟩
    have hct : (c / t) * t = c := div_mul_cancel₀ c ht
    have := congrArg Subtype.val hct
    show S.B v (((c / t : S.F) : K) * y) = (c : K)
    rw [S.B_smul_right _ (c / t).2]
    simpa using this
  rw [hrange, finrank_top, finrank_self, S.finrank_K] at hrank
  omega

theorem gq_ax (x : ℙ S.F K) (l : S.TILine) (hx : x ∉ l) :
    ∃ y : ℙ S.F K, y ∈ l ∧ ∃ m : S.TILine, x ∈ m ∧ y ∈ m := by
  have hv : x.rep ≠ 0 := x.rep_nonzero
  have hW3 := S.finrank_ker_Bfun hv
  have hinf : 0 < finrank S.F ↥(l.1 ⊓ LinearMap.ker (S.Bfun x.rep)) := by
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq l.1 (LinearMap.ker (S.Bfun x.rep))
    have hle := Submodule.finrank_le (l.1 ⊔ LinearMap.ker (S.Bfun x.rep))
    rw [S.finrank_K] at hle
    rw [l.2.1, hW3] at hsum
    omega
  have hne : l.1 ⊓ LinearMap.ker (S.Bfun x.rep) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hinf
    omega
  obtain ⟨w, hwI, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hwl : w ∈ l.1 := (Submodule.mem_inf.mp hwI).1
  have hwW : S.B x.rep w = 0 :=
    (S.Bfun_apply x.rep w).mp (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hwI).2)
  let y : ℙ S.F K := Projectivization.mk S.F w hw0
  have hysub : y.submodule = S.F ∙ w := Projectivization.submodule_mk _ _
  have hyl : y ∈ l := by
    show y.submodule ≤ l.1
    rw [hysub, Submodule.span_singleton_le_iff_mem]
    exact hwl
  have hxy : x ≠ y := fun h => hx (h ▸ hyl)
  have hxyB : S.B x.rep y.rep = 0 := by
    have hyrep := S.rep_mem' y
    rw [hysub] at hyrep
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hyrep
    rw [← hc]
    show S.B x.rep ((c : K) * w) = 0
    rw [S.B_smul_right _ c.2, hwW, mul_zero]
  exact ⟨y, hyl, S.lineOf hxy hxyB, (S.mem_lineOf hxy hxyB).1, (S.mem_lineOf hxy hxyB).2⟩

instance : Finite S.TILine :=
  Finite.of_injective (fun l : S.TILine => (l.1 : Set K))
    (fun a b h => Subtype.ext (SetLike.coe_injective h))

theorem card_erase_add_one {α : Type*} [Finite α] (P : α → Prop) (a : α) (ha : P a) :
    Nat.card {y // P y ∧ y ≠ a} + 1 = Nat.card {y // P y} := by
  have e1 : {y | P y} \ {a} = {y | P y ∧ y ≠ a} := by ext y; simp
  have h1 : Nat.card {y // P y ∧ y ≠ a} = Set.ncard {y | P y ∧ y ≠ a} := Nat.card_coe_set_eq _
  have h2 : Nat.card {y // P y} = Set.ncard {y | P y} := Nat.card_coe_set_eq _
  rw [h1, h2, ← e1]
  exact Set.ncard_diff_singleton_add_one ha (Set.toFinite _)

theorem points_in_ker_iff (x y : ℙ S.F K) :
    y.submodule ≤ LinearMap.ker (S.Bfun x.rep) ↔ S.B x.rep y.rep = 0 := by
  constructor
  · intro h
    exact (S.Bfun_apply x.rep y.rep).mp (LinearMap.mem_ker.mp (h (S.rep_mem' y)))
  · intro h b hb
    exact LinearMap.mem_ker.mpr ((S.Bfun_apply x.rep b).mpr (S.B_cross_pts x y h hb))

/-- Each point lies on `q + 1` lines. -/
theorem lines_on_pt (x : ℙ S.F K) : Nat.card {l : S.TILine // x ∈ l} = S.q + 1 := by
  classical
  have hv : x.rep ≠ 0 := x.rep_nonzero
  have hW3 : finrank S.F (LinearMap.ker (S.Bfun x.rep)) = 3 := S.finrank_ker_Bfun hv
  have hxW : x.submodule ≤ LinearMap.ker (S.Bfun x.rep) :=
    (S.points_in_ker_iff x x).mpr (S.B_self _)
  -- the points of `W = x^⊥` other than `x`: `q² + q` of them
  have hZ : Nat.card {y : ℙ S.F K // y.submodule ≤ LinearMap.ker (S.Bfun x.rep) ∧ y ≠ x}
      = S.q + S.q ^ 2 := by
    have h1 := card_erase_add_one
      (fun y : ℙ S.F K => y.submodule ≤ LinearMap.ker (S.Bfun x.rep)) x hxW
    have h2 : Nat.card {y : ℙ S.F K // y.submodule ≤ LinearMap.ker (S.Bfun x.rep)}
        = 1 + S.q + S.q ^ 2 := by
      rw [S.card_points_le _, Projectivization.card_of_finrank S.F _ hW3]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, S.natCard_F]
      ring
    omega
  -- the line through `x` and `y`
  let f : {y : ℙ S.F K // y.submodule ≤ LinearMap.ker (S.Bfun x.rep) ∧ y ≠ x} →
      {l : S.TILine // x ∈ l} := fun y =>
    ⟨S.lineOf (fun h => y.2.2 h.symm) ((S.points_in_ker_iff x y.1).mp y.2.1),
      (S.mem_lineOf _ _).1⟩
  have hfiber : ∀ l : {l : S.TILine // x ∈ l},
      Nat.card {y : {y : ℙ S.F K // y.submodule ≤ LinearMap.ker (S.Bfun x.rep) ∧ y ≠ x} //
        f y = l} = S.q := by
    intro l
    have hcount := card_erase_add_one (fun z : ℙ S.F K => z.submodule ≤ l.1.1) x l.2
    have hcard : Nat.card {z : ℙ S.F K // z.submodule ≤ l.1.1} = S.q + 1 :=
      S.card_points_on l.1.1 l.1.2.1
    have hxrep : x.rep ∈ l.1.1 := l.2 (S.rep_mem' x)
    have hto : ∀ y : {y : ℙ S.F K // y.submodule ≤ LinearMap.ker (S.Bfun x.rep) ∧ y ≠ x},
        f y = l → y.1.submodule ≤ l.1.1 := by
      intro y hy
      have hle : y.1.submodule ≤ (f y).1.1 :=
        (S.mem_lineOf (fun h => y.2.2 h.symm) ((S.points_in_ker_iff x y.1).mp y.2.1)).2
      rw [hy] at hle
      exact hle
    have e : {y : {y : ℙ S.F K // y.submodule ≤ LinearMap.ker (S.Bfun x.rep) ∧ y ≠ x} //
        f y = l} ≃ {z : ℙ S.F K // z.submodule ≤ l.1.1 ∧ z ≠ x} :=
      { toFun := fun y => ⟨y.1.1, hto y.1 y.2, y.1.2.2⟩
        invFun := fun z =>
          have hzl : z.1.submodule ≤ l.1.1 := z.2.1
          have hB : S.B x.rep z.1.rep = 0 :=
            l.1.2.2 _ hxrep _ (hzl (S.rep_mem' z.1))
          ⟨⟨z.1, (S.points_in_ker_iff x z.1).mpr hB, z.2.2⟩,
            Subtype.ext (S.lineOf_eq (fun h => z.2.2 h.symm) hB l.1 l.2 hzl)⟩
        left_inv := fun y => Subtype.ext (Subtype.ext rfl)
        right_inv := fun z => Subtype.ext rfl }
    rw [Nat.card_congr e]
    omega
  have : Fintype {l : S.TILine // x ∈ l} := Fintype.ofFinite _
  have htot : Nat.card {y : ℙ S.F K // y.submodule ≤ LinearMap.ker (S.Bfun x.rep) ∧ y ≠ x}
      = Nat.card {l : S.TILine // x ∈ l} * S.q := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
    simp only [hfiber, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [Nat.card_eq_fintype_card]
  rw [hZ] at htot
  have hpos : 0 < S.q := by have := S.one_lt_q; omega
  have hmul : Nat.card {l : S.TILine // x ∈ l} * S.q = (S.q + 1) * S.q := by
    rw [← htot]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

end Setting

end BipartiteDD.SingerC

namespace BipartiteDD.SingerC

open scoped LinearAlgebra.Projectivization

variable {K : Type*} [Field K] [Fintype K] {p : ℕ} [Fact p.Prime] [CharP K p]

/-- The lines of `W(3,q)` on the Singer setting: the totally isotropic 2-dimensional `F`-subspaces
of `K`. -/
abbrev W3Line (S : Setting K p) : Type _ := S.TILine

/-- Target 1: `W(3,q)` on the Singer setting is a generalized quadrangle of order `(q, q)`. -/
theorem W3.isGQst (S : Setting K p) : GQst (ℙ S.F K) (W3Line S) S.q S.q :=
  ⟨S.pts_on_line, S.lines_on_pt, S.one_line, S.gq_ax⟩

end BipartiteDD.SingerC
