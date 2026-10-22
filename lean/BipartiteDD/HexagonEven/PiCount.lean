import BipartiteDD.HexagonEven.Pi

/-! Theorem D (even `q`), part 5 (mirror of `HexagonD/PiCount.lean`): counting the singular points of `Π_d`.

For `F` finite with `t² + t + d` anisotropic (`hd`), `Π_d ∩ Q` is an elliptic quadric `Q⁻(5, q)`: it has
`(q³ + 1)(q + 1)` points (`card_pointsPiE`). Coordinates on `Π_d`: `x₀ = -x₃ - d x₄`, free `(x₁, x₅)`, `(x₂, x₆)`,
`(x₃, x₄)`; then `Q = x₁x₅ + x₂x₆ + g(x₃, x₄)` with `g(a, b) = -(a² + ab + d b²)` anisotropic. -/

namespace BipartiteDD.HexagonEven

open BipartiteDD.Hexagon Module Submodule

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Coordinates on `Π_d`: `x₀ = -x₃ - d x₄`, then `(x₁, x₅), (x₂, x₆), (x₃, x₄)`. -/
def ePiE (d : F) : {x : V7 F // x 0 + x 3 + d * x 4 = 0} ≃ (F × F) × ((F × F) × (F × F)) where
  toFun x := ((x.1 1, x.1 5), ((x.1 2, x.1 6), (x.1 3, x.1 4)))
  invFun t := ⟨![-t.2.2.1 - d * t.2.2.2, t.1.1, t.2.1.1, t.2.2.1, t.2.2.2, t.1.2, t.2.1.2], by simp <;> ring⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    have := x.2
    fin_cases i <;> simp <;> linear_combination -this
  right_inv t := by rfl

/-- The anisotropic binary part `g(a, b) = -(a² + ab + d b²)`. -/
def gE (d : F) (u : F × F) : F := -(u.1 ^ 2 + u.1 * u.2 + d * u.2 ^ 2)

theorem card_gE {d : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) :
    Fintype.card {u : F × F // gE d u = 0} = 1 := by
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨(0, 0), by simp [gE]⟩, ?_⟩
  rintro ⟨⟨a, b⟩, h⟩
  apply Subtype.ext
  simp only [gE] at h
  have h' : a ^ 2 + a * b + d * b ^ 2 = 0 := by linear_combination -h
  have hb : b = 0 := by
    by_contra hb
    apply hd (a / b)
    field_simp
    linear_combination h'
  subst hb
  have : a = 0 := by simpa using h'
  simp [this]

theorem Qf_eq_hypE (d : F) (x : {x : V7 F // x 0 + x 3 + d * x 4 = 0}) :
    Qf x.1 = hyp (hyp (gE d)) (ePiE d x) := by
  have := x.2
  change _ = x.1 1 * x.1 5 + (x.1 2 * x.1 6 + -(x.1 3 ^ 2 + x.1 3 * x.1 4 + d * x.1 4 ^ 2))
  unfold Qf
  linear_combination (x.1 4) * this

/-- `Π_d ∩ Q` has `q⁵ - q³ + q²` vectors (stated without subtraction). -/
theorem card_zeros_PiE {d : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) :
    Fintype.card {x : V7 F // x 0 + x 3 + d * x 4 = 0 ∧ Qf x = 0} + Fintype.card F ^ 3 =
      Fintype.card F ^ 5 + Fintype.card F ^ 2 := by
  have e1 : {x : V7 F // x 0 + x 3 + d * x 4 = 0 ∧ Qf x = 0} ≃
      {t : (F × F) × ((F × F) × (F × F)) // hyp (hyp (gE d)) t = 0} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun x : V7 F => x 0 + x 3 + d * x 4 = 0)
      (fun x => Qf x = 0)).symm.trans
      ((ePiE d).subtypeEquiv (fun x => by rw [Qf_eq_hypE d x]))
  rw [Fintype.card_congr e1, card_hyp, card_hyp, card_gE hd]
  simp only [Fintype.card_prod]
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card F = r + 1 :=
    Nat.exists_eq_add_one_of_ne_zero Fintype.card_ne_zero
  rw [hr, Nat.add_sub_cancel]
  ring

/-- The singular points of `Π_d`. -/
abbrev PtPiE (d : F) : Type _ := {p : SPt F // p.1.rep 0 + p.1.rep 3 + d * p.1.rep 4 = 0}

/-- The nonzero singular vectors of `Π_d` are (point of `Π_d ∩ Q`) × (unit). -/
noncomputable def ptPiUnitsEquivE (d : F) :
    PtPiE d × Fˣ ≃ {x : V7 F // x ≠ 0 ∧ Qf x = 0 ∧ x 0 + x 3 + d * x 4 = 0} :=
  Equiv.ofBijective
    (fun pa => ⟨(pa.2 : F) • pa.1.1.1.rep, smul_ne_zero pa.2.ne_zero pa.1.1.1.rep_nonzero, by
        rw [Qf_smul, pa.1.1.2, mul_zero], by
        have := pa.1.2
        simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination (pa.2 : F) * this⟩)
    (by
      constructor
      · rintro ⟨p, a⟩ ⟨p', a'⟩ h
        have hv : (a : F) • p.1.1.rep = (a' : F) • p'.1.1.rep := congrArg Subtype.val h
        have h' := sptProdUnitsEquiv.injective (a₁ := (p.1, a)) (a₂ := (p'.1, a')) (Subtype.ext hv)
        simp only [Prod.mk.injEq] at h'
        exact Prod.ext (Subtype.ext h'.1) h'.2
      · rintro ⟨v, hv0, hvq, hvL⟩
        obtain ⟨⟨p, a⟩, hpa⟩ := sptProdUnitsEquiv.surjective ⟨v, hv0, hvq⟩
        have hv : (a : F) • p.1.rep = v := congrArg Subtype.val hpa
        have hp : p.1.rep 0 + p.1.rep 3 + d * p.1.rep 4 = 0 := by
          have : (a : F) * (p.1.rep 0 + p.1.rep 3 + d * p.1.rep 4) = 0 := by
            rw [← hv] at hvL
            simp only [Pi.smul_apply, smul_eq_mul] at hvL
            linear_combination hvL
          exact (mul_eq_zero.1 this).resolve_left a.ne_zero
        refine ⟨(⟨p, hp⟩, a), ?_⟩
        apply Subtype.ext
        exact hv)

noncomputable instance (d : F) : Fintype (PtPiE d) := Fintype.ofFinite _

theorem card_pointsPiE {d : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) :
    Fintype.card (PtPiE d) = (Fintype.card F ^ 3 + 1) * (Fintype.card F + 1) := by
  have h1 := Fintype.card_congr (ptPiUnitsEquivE d)
  rw [Fintype.card_prod, Fintype.card_units] at h1
  have h2 : Fintype.card {x : V7 F // x ≠ 0 ∧ Qf x = 0 ∧ x 0 + x 3 + d * x 4 = 0} + 1 =
      Fintype.card {x : V7 F // x 0 + x 3 + d * x 4 = 0 ∧ Qf x = 0} := by
    simp only [Fintype.card_subtype]
    have : (Finset.univ.filter fun x : V7 F => x 0 + x 3 + d * x 4 = 0 ∧ Qf x = 0) =
        insert 0 (Finset.univ.filter fun x : V7 F => x ≠ 0 ∧ Qf x = 0 ∧ x 0 + x 3 + d * x 4 = 0) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_univ, true_and]
      by_cases hx : x = 0
      · subst hx; simp [Qf]
      · simp [hx, and_comm]
    rw [this, Finset.card_insert_of_notMem (by simp)]
  have h3 := card_zeros_PiE hd
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card F = r + 2 :=
    ⟨Fintype.card F - 2, by have := Fintype.one_lt_card (α := F); omega⟩
  have hq1 : Fintype.card F - 1 = r + 1 := by omega
  rw [hq1] at h1
  rw [hr] at h3 ⊢
  have key : Fintype.card (PtPiE d) * (r + 1) = ((r + 2) ^ 3 + 1) * (r + 2 + 1) * (r + 1) := by
    zify at h1 h2 h3 ⊢
    linear_combination h1 + h2 + h3
  exact Nat.eq_of_mul_eq_mul_right (by omega) key

end BipartiteDD.HexagonEven
