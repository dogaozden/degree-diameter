import BipartiteDD.Haar.PGL37

/-! Nat-level matrix arithmetic for `PGL(2, 37)`, and its bridge to the group.

The kernel check of the (6,10) record (`D6D10.Check`) multiplies Nat quadruples `(a, b, c, d)` with the entries
reduced mod 37: that is much cheaper in the kernel than the group operations. This file proves that the
evaluation agrees with the group: `gM (prodN L) = (L.map gM).prod` for lists `L` of nonsingular quadruples, and
`gM (normN x) = gM x`. `gM` is `PGL37.gM`, the group element with the given Nat entries. -/

namespace BipartiteDD.Haar.PGL37

/-- The product of two Nat matrices, entries reduced mod 37. -/
def mN (x y : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  ((x.1 * y.1 + x.2.1 * y.2.2.1) % 37, (x.1 * y.2.1 + x.2.1 * y.2.2.2) % 37,
    (x.2.2.1 * y.1 + x.2.2.2 * y.2.2.1) % 37, (x.2.2.1 * y.2.1 + x.2.2.2 * y.2.2.2) % 37)

/-- The adjugate `(d, -b, -c, a)` mod 37: a representative of the inverse class. -/
def adjN (x : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (x.2.2.2, (37 - x.2.1) % 37, (37 - x.2.2.1) % 37, x.1)

/-- The leading entry mod 37: `a` when `a ≠ 0`, else `c`. -/
def leadN (a c : ℕ) : ℕ := if a % 37 = 0 then c % 37 else a % 37

/-- A scalar multiple of `x` (by the inverse of its leading entry), a representative of its class. -/
def normN (x : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  ((invN (leadN x.1 x.2.2.1) * x.1) % 37, (invN (leadN x.1 x.2.2.1) * x.2.1) % 37,
    (invN (leadN x.1 x.2.2.1) * x.2.2.1) % 37, (invN (leadN x.1 x.2.2.1) * x.2.2.2) % 37)

/-- The determinant of a Nat quadruple, in `ZMod 37`. -/
def detZ (M : ℕ × ℕ × ℕ × ℕ) : ZMod 37 :=
  (M.1 : ZMod 37) * (M.2.2.2 : ZMod 37) - (M.2.1 : ZMod 37) * (M.2.2.1 : ZMod 37)

/-- The product of a list of Nat matrices, right to left, from the identity. -/
def prodN : List (ℕ × ℕ × ℕ × ℕ) → ℕ × ℕ × ℕ × ℕ
  | [] => (1, 0, 0, 1)
  | M :: L => mN M (prodN L)

/-- The group element of a Nat quadruple: `gM M = [M]` in `PGL(2, 37)`. -/
theorem gM_def (M : ℕ × ℕ × ℕ × ℕ) :
    gM M = gZ (M.1 : ZMod 37) (M.2.1 : ZMod 37) (M.2.2.1 : ZMod 37) (M.2.2.2 : ZMod 37) := rfl

theorem mk_mul_mk {a b c d a' b' c' d' : ZMod 37} (h : a * d - b * c ≠ 0) (h' : a' * d' - b' * c' ≠ 0) :
    mk a b c d h * mk a' b' c' d' h'
      = mk (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') (mul_det h h') := by
  exact mk_congr (zm_mul_ne _ _ (lam_ne h) (lam_ne h')) (mul_det h h') _ (by simp only [mk]; ring)
    (by simp only [mk]; ring) (by simp only [mk]; ring) (by simp only [mk]; ring)

theorem gZ_mul {a b c d a' b' c' d' : ZMod 37} (h : a * d - b * c ≠ 0) (h' : a' * d' - b' * c' ≠ 0) :
    gZ (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d')
      = gZ a b c d * gZ a' b' c' d' := by
  have h1 := mul_det h h'
  unfold gZ
  rw [dif_pos h, dif_pos h', dif_pos h1]
  exact (mk_mul_mk h h').symm

theorem gZ_inv {a b c d : ZMod 37} (h : a * d - b * c ≠ 0) : (gZ a b c d)⁻¹ = gZ d (-b) (-c) a := by
  have h' : d * a - (-b) * (-c) ≠ 0 := inv_det h
  unfold gZ
  rw [dif_pos h, dif_pos h']
  exact mk_congr (lam_ne h) h' _ rfl (by simp only [mk]; ring) (by simp only [mk]; ring) rfl

theorem gZ_scale {a b c d μ : ZMod 37} (hμ : μ ≠ 0) (h : a * d - b * c ≠ 0) :
    gZ (μ * a) (μ * b) (μ * c) (μ * d) = gZ a b c d := by
  unfold gZ
  rw [dif_pos (scale_det hμ h), dif_pos h]
  exact mk_scale hμ h

theorem neg_cast (b : ℕ) (hb : b < 37) : ((37 - b : ℕ) : ZMod 37) = -(b : ZMod 37) := by
  rw [Nat.cast_sub (by omega : b ≤ 37), ZMod.natCast_self, zero_sub]

theorem detZ_mN (x y : ℕ × ℕ × ℕ × ℕ) : detZ (mN x y) = detZ x * detZ y := by
  simp only [detZ, mN, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]
  ring

theorem detZ_adjN (x : ℕ × ℕ × ℕ × ℕ) (hb : x.2.1 < 37) (hc : x.2.2.1 < 37) :
    detZ (adjN x) = detZ x := by
  simp only [detZ, adjN, ZMod.natCast_mod]
  rw [neg_cast _ hb, neg_cast _ hc]
  ring

theorem gM_mN (x y : ℕ × ℕ × ℕ × ℕ) (hx : detZ x ≠ 0) (hy : detZ y ≠ 0) :
    gM (mN x y) = gM x * gM y := by
  have hx' : (x.1 : ZMod 37) * (x.2.2.2 : ZMod 37) - (x.2.1 : ZMod 37) * (x.2.2.1 : ZMod 37) ≠ 0 := hx
  have hy' : (y.1 : ZMod 37) * (y.2.2.2 : ZMod 37) - (y.2.1 : ZMod 37) * (y.2.2.1 : ZMod 37) ≠ 0 := hy
  rw [gM_def, gM_def, gM_def]
  simp only [mN, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]
  exact gZ_mul hx' hy'

theorem gM_adjN (x : ℕ × ℕ × ℕ × ℕ) (hx : detZ x ≠ 0) (hb : x.2.1 < 37) (hc : x.2.2.1 < 37) :
    gM (adjN x) = (gM x)⁻¹ := by
  have hx' : (x.1 : ZMod 37) * (x.2.2.2 : ZMod 37) - (x.2.1 : ZMod 37) * (x.2.2.1 : ZMod 37) ≠ 0 := hx
  rw [gM_def, gM_def, gZ_inv hx']
  simp only [adjN, ZMod.natCast_mod]
  rw [neg_cast _ hb, neg_cast _ hc]

theorem lead_cast (a c : ℕ) : ((leadN a c : ℕ) : ZMod 37) = lead (a : ZMod 37) (c : ZMod 37) := by
  unfold leadN lead
  by_cases ha : a % 37 = 0
  · have ha' : (a : ZMod 37) = 0 := by
      rw [← ZMod.natCast_mod a 37, ha, Nat.cast_zero]
    rw [if_pos ha, if_pos ha', ZMod.natCast_mod]
  · have ha' : (a : ZMod 37) ≠ 0 := by
      intro h0
      apply ha
      have := ZMod.val_natCast (n := 37) a
      rw [h0, ZMod.val_zero] at this
      exact this.symm
    rw [if_neg ha, if_neg ha', ZMod.natCast_mod]

theorem invN_ne : ∀ x : ℕ, x < 37 → x ≠ 0 → ((invN x : ℕ) : ZMod 37) ≠ 0 := by
  decide

theorem leadN_lt (a c : ℕ) : leadN a c < 37 := by
  unfold leadN
  split_ifs
  · exact Nat.mod_lt _ (by norm_num)
  · exact Nat.mod_lt _ (by norm_num)

theorem normN_scalar (x : ℕ × ℕ × ℕ × ℕ) (hx : detZ x ≠ 0) :
    ((invN (leadN x.1 x.2.2.1) : ℕ) : ZMod 37) ≠ 0 := by
  have hL : ((leadN x.1 x.2.2.1 : ℕ) : ZMod 37) ≠ 0 := by
    rw [lead_cast]
    apply lead_ne (b := (x.2.1 : ZMod 37)) (d := (x.2.2.2 : ZMod 37))
    exact hx
  have hL0 : leadN x.1 x.2.2.1 ≠ 0 := by
    intro h
    apply hL
    rw [h, Nat.cast_zero]
  exact invN_ne _ (leadN_lt _ _) hL0

theorem gM_normN (x : ℕ × ℕ × ℕ × ℕ) (hx : detZ x ≠ 0) : gM (normN x) = gM x := by
  have hx' : (x.1 : ZMod 37) * (x.2.2.2 : ZMod 37) - (x.2.1 : ZMod 37) * (x.2.2.1 : ZMod 37) ≠ 0 := hx
  rw [gM_def, gM_def]
  simp only [normN, ZMod.natCast_mod, Nat.cast_mul]
  exact gZ_scale (normN_scalar x hx) hx'

theorem detZ_prodN (L : List (ℕ × ℕ × ℕ × ℕ)) (h : ∀ M ∈ L, detZ M ≠ 0) : detZ (prodN L) ≠ 0 := by
  induction L with
  | nil =>
    show detZ (1, 0, 0, 1) ≠ 0
    unfold detZ
    decide
  | cons M L ih =>
    have hM : detZ M ≠ 0 := h M (List.mem_cons_self ..)
    have hL : detZ (prodN L) ≠ 0 := ih (fun N hN => h N (List.mem_cons_of_mem _ hN))
    show detZ (mN M (prodN L)) ≠ 0
    rw [detZ_mN]
    exact zm_mul_ne _ _ hM hL

theorem gM_prodN (L : List (ℕ × ℕ × ℕ × ℕ)) (h : ∀ M ∈ L, detZ M ≠ 0) :
    gM (prodN L) = (L.map gM).prod := by
  induction L with
  | nil =>
    show gM (1, 0, 0, 1) = 1
    rw [gM_def]
    unfold gZ
    rw [dif_pos (by decide)]
    rfl
  | cons M L ih =>
    have hM : detZ M ≠ 0 := h M (List.mem_cons_self ..)
    have hL : ∀ N ∈ L, detZ N ≠ 0 := fun N hN => h N (List.mem_cons_of_mem _ hN)
    rw [List.map_cons, List.prod_cons]
    show gM (mN M (prodN L)) = gM M * (L.map gM).prod
    rw [gM_mN M (prodN L) hM (detZ_prodN L hL), ih hL]

end BipartiteDD.Haar.PGL37
