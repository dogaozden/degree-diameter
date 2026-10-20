import BipartiteDD.Hexagon.Defs

/-! Split Cayley hexagon `H(q)`: counting the points of the parabolic quadric `Q(6, q)`.

Over a finite field `F` with `q` elements (any characteristic):
* `card_zeros_Qf`: the form `Qf` has exactly `q⁶` zeros in `F⁷`;
* `card_spt`: `|Q(6, q)| · (q - 1) = q⁶ - 1`, hence `|Q(6, q)| = (q⁶ - 1)/(q - 1)`;
* `card_spt_eq`: `|Q(6, q)| = (q + 1)(1 + q² + q⁴)`.

The zero count uses the hyperbolic-pair recursion: adding a hyperbolic pair `ab` to a function
`g : S → F` gives `#{ab + g s = 0} = q · #{g = 0} + (q - 1)·|S|`, since `#{(a, b) | ab = c}` is
`q - 1` for `c ≠ 0` and `2q - 1` for `c = 0`. -/

namespace BipartiteDD.Hexagon

open Finset

section Count

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Add one hyperbolic pair to a function `g : S → F`: `((a, b), s) ↦ a * b + g s`. -/
def hyp {S : Type*} (g : S → F) (t : (F × F) × S) : F := t.1.1 * t.1.2 + g t.2

/-- `#{(a, b) | a * b + d = 0} = (q - 1) + (q if d = 0 else 0)`. -/
theorem sum_mul_add_eq_zero (d : F) :
    (∑ a : F, ∑ b : F, if a * b + d = 0 then 1 else 0 : ℕ) =
      (Fintype.card F - 1) + if d = 0 then Fintype.card F else 0 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : F))]
  have h1 : ∀ a ∈ (univ : Finset F).erase 0,
      (∑ b : F, if a * b + d = 0 then 1 else 0 : ℕ) = 1 := by
    intro a ha
    have ha : a ≠ 0 := Finset.ne_of_mem_erase ha
    have : ∀ b, (a * b + d = 0 ↔ b = -d / a) := by
      intro b
      constructor
      · intro h
        field_simp
        linear_combination h
      · rintro rfl
        field_simp
        ring
    simp_rw [this]
    simp
  rw [Finset.sum_congr rfl h1]
  simp only [zero_mul, zero_add, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    Finset.card_erase_of_mem (Finset.mem_univ _)]
  split_ifs <;> simp [add_comm]

/-- The hyperbolic-pair recursion. -/
theorem card_hyp {S : Type*} [Fintype S] (g : S → F) :
    Fintype.card {t // hyp g t = 0} =
      Fintype.card F * Fintype.card {s // g s = 0} + (Fintype.card F - 1) * Fintype.card S := by
  rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card_filter, Finset.card_filter,
    Fintype.sum_prod_type_right]
  simp only [Fintype.sum_prod_type]
  rw [show (∑ s : S, ∑ a : F, ∑ b : F, if hyp g ((a, b), s) = 0 then 1 else 0 : ℕ) =
      ∑ s : S, ((Fintype.card F - 1) + if g s = 0 then Fintype.card F else 0) from
    Finset.sum_congr rfl (fun s _ => sum_mul_add_eq_zero (g s)), Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Finset.sum_ite]
  ring

/-- `F⁷` as three hyperbolic pairs and one extra coordinate. -/
def e7 : V7 F ≃ (F × F) × ((F × F) × ((F × F) × F)) where
  toFun x := ((x 0, x 4), ((x 1, x 5), ((x 2, x 6), x 3)))
  invFun t := ![t.1.1, t.2.1.1, t.2.2.1.1, t.2.2.2, t.1.2, t.2.1.2, t.2.2.1.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv t := rfl

/-- The anisotropic part `x₃ ↦ -x₃²`. -/
def g0 (x : F) : F := -x ^ 2

omit [Fintype F] [DecidableEq F] in
theorem Qf_eq_hyp (x : V7 F) : Qf x = hyp (hyp (hyp g0)) (e7 x) := by
  change _ = x 0 * x 4 + (x 1 * x 5 + (x 2 * x 6 + -x 3 ^ 2))
  unfold Qf
  ring

theorem card_g0 : Fintype.card {x : F // g0 x = 0} = 1 := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (q := fun x : F => x = 0) (fun x => by
    simp [g0]))]
  exact Fintype.card_subtype_eq 0

/-- The quadric form `Qf` has exactly `q⁶` zeros in `F⁷`. -/
theorem card_zeros_Qf : Fintype.card {x : V7 F // Qf x = 0} = Fintype.card F ^ 6 := by
  rw [Fintype.card_congr (e7.subtypeEquiv (p := fun x => Qf x = 0)
    (q := fun t => hyp (hyp (hyp g0)) t = 0) (fun x => by rw [Qf_eq_hyp]))]
  rw [card_hyp, card_hyp, card_hyp, card_g0]
  simp only [Fintype.card_prod]
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card F = r + 1 :=
    Nat.exists_eq_add_one_of_ne_zero Fintype.card_ne_zero
  rw [hr, Nat.add_sub_cancel]
  ring

/-- The nonzero zeros of `Qf`: `q⁶ - 1` of them. -/
theorem card_nonzero_zeros_Qf :
    Fintype.card {x : V7 F // x ≠ 0 ∧ Qf x = 0} = Fintype.card F ^ 6 - 1 := by
  rw [← card_zeros_Qf]
  simp only [Fintype.card_subtype]
  have : (univ.filter fun x : V7 F => x ≠ 0 ∧ Qf x = 0) =
      (univ.filter fun x : V7 F => Qf x = 0).erase 0 := by
    ext x
    simp [and_comm]
  rw [this, Finset.card_erase_of_mem]
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, by simp [Qf]⟩

end Count

section Points

variable {F : Type*} [Field F]

/-- Being on the quadric does not depend on the representative. -/
theorem Qf_rep_eq_zero_iff (v : V7 F) (hv : v ≠ 0) :
    Qf (Projectivization.mk F v hv).rep = 0 ↔ Qf v = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F v hv
  rw [← ha, Units.smul_def, Qf_smul]
  simp [a.ne_zero]

/-- Nonzero singular vectors are (singular point) × (scalar). -/
noncomputable def sptProdUnitsEquiv : SPt F × Fˣ ≃ {x : V7 F // x ≠ 0 ∧ Qf x = 0} :=
  Equiv.ofBijective
    (fun pc => ⟨(pc.2 : F) • pc.1.1.rep, smul_ne_zero pc.2.ne_zero pc.1.1.rep_nonzero, by
      rw [Qf_smul, pc.1.2, mul_zero]⟩)
    (by
      constructor
      · rintro ⟨⟨p, hp⟩, c⟩ ⟨⟨p', hp'⟩, c'⟩ h
        simp only [Subtype.mk.injEq] at h
        have hmk : ∀ (p : Projectivization F (V7 F)) (c : Fˣ),
            Projectivization.mk F ((c : F) • p.rep) (smul_ne_zero c.ne_zero p.rep_nonzero) = p := by
          intro p c
          conv_rhs => rw [← Projectivization.mk_rep p]
          exact (Projectivization.mk_eq_mk_iff F _ _ _ _).2 ⟨c, rfl⟩
        have hpp : p = p' := by
          rw [← hmk p c, ← hmk p' c']
          simp only [h]
        subst hpp
        have hcc : (c : F) = c' := smul_left_injective F p.rep_nonzero h
        simp only [Prod.mk.injEq, true_and]
        exact Units.ext hcc
      · rintro ⟨v, hv0, hvq⟩
        obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F v hv0
        refine ⟨(⟨Projectivization.mk F v hv0, (Qf_rep_eq_zero_iff v hv0).2 hvq⟩, a⁻¹), ?_⟩
        simp only [Subtype.mk.injEq]
        rw [← ha, ← Units.smul_def, inv_smul_smul])

variable [Fintype F]

instance finite_spt : Finite (SPt F) := Subtype.finite

noncomputable instance fintype_spt : Fintype (SPt F) := Fintype.ofFinite _

variable [DecidableEq F]

/-- `|Q(6, q)| · (q - 1) = q⁶ - 1`. -/
theorem card_spt : Nat.card (SPt F) * (Fintype.card F - 1) = Fintype.card F ^ 6 - 1 := by
  have h := Nat.card_congr (sptProdUnitsEquiv (F := F))
  rw [Nat.card_prod, Nat.card_units,
    Nat.card_eq_fintype_card (α := {x : V7 F // x ≠ 0 ∧ Qf x = 0}),
    Nat.card_eq_fintype_card (α := F), card_nonzero_zeros_Qf] at h
  exact h

/-- `|Q(6, q)| = (q⁶ - 1) / (q - 1)`. -/
theorem card_spt_div :
    Nat.card (SPt F) = (Fintype.card F ^ 6 - 1) / (Fintype.card F - 1) := by
  have hq : 0 < Fintype.card F - 1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  rw [← card_spt, Nat.mul_div_cancel _ hq]

/-- `|Q(6, q)| = (q + 1)(1 + q² + q⁴)`. -/
theorem card_spt_eq :
    Nat.card (SPt F) = (Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4) := by
  have hq : 0 < Fintype.card F - 1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  refine Nat.eq_of_mul_eq_mul_right hq ?_
  rw [card_spt]
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card F = r + 1 :=
    Nat.exists_eq_add_one_of_ne_zero Fintype.card_ne_zero
  rw [hr, Nat.add_sub_cancel]
  refine Nat.sub_eq_of_eq_add ?_
  ring

/-- `|Q(6, q)| = 1 + q + q² + q³ + q⁴ + q⁵`. -/
theorem card_spt_eq' :
    Nat.card (SPt F) = 1 + Fintype.card F + Fintype.card F ^ 2 + Fintype.card F ^ 3 +
      Fintype.card F ^ 4 + Fintype.card F ^ 5 := by
  rw [card_spt_eq]
  ring

end Points

end BipartiteDD.Hexagon
