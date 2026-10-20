import BipartiteDD.SingerC.W3Spread

/-! Corollary C1, step 3 (work in progress): the 2-ovoid `O` of W(3,q), and counting vectors and
points of a subspace in a class. -/

namespace BipartiteDD.SingerC

open Module Projectivization
open scoped LinearAlgebra.Projectivization

namespace Setting

variable {K : Type*} [Field K] [Fintype K] {p : ℕ} [Fact p.Prime] [CharP K p]
variable (S : Setting K p)

/-- Scaling by a nonzero scalar of `F` keeps a vector in its class. -/
theorem inClass_mul_F {a : ℕ} (ha : a < S.q + 1) {c z : K} (hc : c ∈ S.F) (hc0 : c ≠ 0)
    (hz : S.InClass a z) : S.InClass a (c * z) := by
  have hz0 : z ≠ 0 := by
    obtain ⟨i, hi, -⟩ := hz
    rw [hi]
    exact pow_ne_zero _ S.g_ne_zero
  obtain ⟨c', hc', hc'0, hn⟩ := (S.inClass_iff ha hz0).mp hz
  refine (S.inClass_iff ha (mul_ne_zero hc0 hz0)).mpr
    ⟨c ^ 2 * c', S.F.mul_mem (S.F.pow_mem hc 2) hc', mul_ne_zero (pow_ne_zero _ hc0) hc'0, ?_⟩
  have hcN : c ^ (S.q ^ 2 + 1) = c ^ 2 := by
    rw [pow_succ, S.mem_L.mp (S.F_le_L hc), sq]
  rw [mul_pow, hcN, hn]
  ring

theorem inClass_mul_F_iff {a : ℕ} (ha : a < S.q + 1) {c z : K} (hc : c ∈ S.F) (hc0 : c ≠ 0) :
    S.InClass a (c * z) ↔ S.InClass a z := by
  constructor
  · intro h
    have := S.inClass_mul_F ha (S.F.inv_mem hc) (inv_ne_zero hc0) h
    rwa [← mul_assoc, inv_mul_cancel₀ hc0, one_mul] at this
  · exact S.inClass_mul_F ha hc hc0

/-- The 2-ovoid predicate: `z` lies in class `a` or class `q - a`. -/
def Oz (a : ℕ) (z : K) : Prop := S.InClass a z ∨ S.InClass (S.q - a) z

theorem Oz_mul_F_iff {a : ℕ} (ha : a ≤ S.q) {c z : K} (hc : c ∈ S.F) (hc0 : c ≠ 0) :
    S.Oz a (c * z) ↔ S.Oz a z := by
  unfold Oz
  rw [S.inClass_mul_F_iff (by omega) hc hc0, S.inClass_mul_F_iff (by omega) hc hc0]

/-- Points of `F^×`-scalar classes: the nonzero vectors of `F · r` form `F^×`. -/
theorem card_nonzero_units : Nat.card {c : S.F // c ≠ 0} = S.q - 1 := by
  have h := card_erase_add_one (fun _ : S.F => True) 0 trivial
  have hF : Nat.card {c : S.F // True} = S.q := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)), S.natCard_F]
  have h' : Nat.card {y // True ∧ y ≠ (0 : S.F)} = Nat.card {c : S.F // c ≠ 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun y => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩))
  omega

/-- The representative of the point of a nonzero vector is a nonzero scalar multiple of it. -/
theorem rep_mk_eq (v : K) (hv : v ≠ 0) :
    ∃ c : K, c ∈ S.F ∧ c ≠ 0 ∧ (Projectivization.mk S.F v hv).rep = c * v := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' S.F _ _ _ _).mp (Projectivization.mk_rep (Projectivization.mk S.F v hv))
  refine ⟨a, a.2, fun h => (Projectivization.mk S.F v hv).rep_nonzero ?_, ha.symm⟩
  rw [← ha]
  show (a : K) • v = 0
  rw [show (a : K) = 0 from h, zero_smul]

/-- Counting nonzero vectors of a subspace by the points they span. -/
theorem card_vec_points (U : Submodule S.F K) (P : K → Prop)
    (hP : ∀ c : K, c ∈ S.F → c ≠ 0 → ∀ z : K, P (c * z) ↔ P z) :
    Nat.card {v : K // v ≠ 0 ∧ v ∈ U ∧ P v} =
      (S.q - 1) * Nat.card {x : ℙ S.F K // x.submodule ≤ U ∧ P x.rep} := by
  classical
  have hrepP : ∀ v : K, ∀ hv : v ≠ 0, P (Projectivization.mk S.F v hv).rep ↔ P v := by
    intro v hv
    obtain ⟨c, hc, hc0, hcv⟩ := S.rep_mk_eq v hv
    rw [hcv]
    exact hP c hc hc0 v
  let g : {v : K // v ≠ 0 ∧ v ∈ U ∧ P v} → {x : ℙ S.F K // x.submodule ≤ U ∧ P x.rep} :=
    fun v => ⟨Projectivization.mk S.F v.1 v.2.1, by
      refine ⟨?_, ?_⟩
      · show (Projectivization.mk S.F v.1 v.2.1).submodule ≤ U
        rw [Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem]
        exact v.2.2.1
      · exact (hrepP v.1 v.2.1).mpr v.2.2.2⟩
  haveI : Fintype {x : ℙ S.F K // x.submodule ≤ U ∧ P x.rep} := Fintype.ofFinite _
  have hfib : ∀ x : {x : ℙ S.F K // x.submodule ≤ U ∧ P x.rep},
      Nat.card {v : {v : K // v ≠ 0 ∧ v ∈ U ∧ P v} // g v = x} = S.q - 1 := by
    intro x
    obtain ⟨hxU, hxP⟩ := x.2
    have hr0 : x.1.rep ≠ 0 := x.1.rep_nonzero
    have hr : Projectivization.mk S.F x.1.rep x.1.rep_nonzero = x.1 := mk_rep x.1
    let f : {c : S.F // c ≠ 0} → {v : {v : K // v ≠ 0 ∧ v ∈ U ∧ P v} // g v = x} :=
      fun c => ⟨⟨(c.1 : K) * x.1.rep, mul_ne_zero (fun h => c.2 (Subtype.ext h)) hr0,
          U.smul_mem c.1 (hxU (S.rep_mem' x.1)), (hP (c.1 : K) c.1.2
            (fun h => c.2 (Subtype.ext h)) _).mpr hxP⟩,
        Subtype.ext (by
          show Projectivization.mk S.F ((c.1 : K) * x.1.rep) _ = x.1
          exact ((Projectivization.mk_eq_mk_iff' S.F _ _ _ _).mpr ⟨c.1, rfl⟩).trans hr)⟩
    have hfbij : Function.Bijective f := by
      constructor
      · intro c c' h
        have h2 : (c.1 : K) * x.1.rep = (c'.1 : K) * x.1.rep := congrArg (fun w => w.1.1) h
        exact Subtype.ext (Subtype.ext (mul_right_cancel₀ hr0 h2))
      · rintro ⟨⟨v, hv0, hvU, hvP⟩, hgv⟩
        have hgv' : Projectivization.mk S.F v hv0 = x.1 := congrArg Subtype.val hgv
        obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' S.F v x.1.rep hv0 hr0).mp (hgv'.trans hr.symm)
        have ha0 : a ≠ 0 := fun h => hv0 (by rw [← ha, h, zero_smul])
        exact ⟨⟨a, ha0⟩, Subtype.ext (Subtype.ext ha)⟩
    rw [← Nat.card_eq_of_bijective f hfbij]
    exact S.card_nonzero_units
  have e1 : Nat.card {v : K // v ≠ 0 ∧ v ∈ U ∧ P v} =
      Nat.card (Σ x : {x : ℙ S.F K // x.submodule ≤ U ∧ P x.rep},
        {v : {v : K // v ≠ 0 ∧ v ∈ U ∧ P v} // g v = x}) :=
    (Nat.card_congr (Equiv.sigmaFiberEquiv g)).symm
  rw [e1, Nat.card_sigma]
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [Nat.card_eq_fintype_card, mul_comm]

end Setting

end BipartiteDD.SingerC
