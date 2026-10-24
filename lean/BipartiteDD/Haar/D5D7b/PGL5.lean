import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! The group `PGL(2, 5)` of order 120, with a computable numbering by `ℕ`.

An element is a matrix `[[a, b], [c, d]]` over `ZMod 5` with `a * d - b * c ≠ 0`, taken modulo scalars. Each
class has one representative with `a = 1`, or with `a = 0` and `c = 1`: the leading entry (`a`, or `c` when `a = 0`)
is scaled to `1`. The product is the matrix product, normalised by `mk`.

The numbering is `enc`/`quadN`: the classes with `a = 1` come first, `n = (c · 5 + b) · 4 + k` with `k = (d - b c - 1).val`
(and `k < 4`, since `d ≠ b c`), then the classes with `a = 0`, `c = 1`: `n = 100 + (b - 1) · 5 + d`.
`quadN` is the Nat-level inverse, used by the kernel check in `D5D7b.Check`; `gM` maps a Nat quadruple to the group
element with those entries. -/

namespace BipartiteDD.Haar.D5D7b.PGL5

theorem zm_mul_ne : ∀ x y : ZMod 5, x ≠ 0 → y ≠ 0 → x * y ≠ 0 := by
  decide

/-- `invTab[x] = x⁻¹` in `ZMod 5` for `x ≠ 0`, and `invTab[0] = 0`. -/
def invTab : List ℕ := [0, 1, 3, 2, 4]

/-- The inverse table as a function on `ℕ`. -/
def invN (x : ℕ) : ℕ := invTab.getD x 0

/-- Inverses in `ZMod 5`: `inv5 x = x⁻¹` for `x ≠ 0`. -/
def inv5 (x : ZMod 5) : ZMod 5 := (invN x.val : ZMod 5)

theorem inv5_mul : ∀ x : ZMod 5, x ≠ 0 → x * inv5 x = 1 := by
  decide

theorem inv5_mul2 : ∀ x y : ZMod 5, x ≠ 0 → y ≠ 0 → inv5 (x * y) = inv5 x * inv5 y := by
  decide

theorem inv5_one : inv5 1 = 1 := by
  decide

/-- The leading entry: `a` when `a ≠ 0`, else `c`. -/
def lead (a c : ZMod 5) : ZMod 5 := if a = 0 then c else a

/-- The scalar that normalises `(a, b, c, d)`. -/
def lam (a c : ZMod 5) : ZMod 5 := inv5 (lead a c)

theorem lead_ne {a b c d : ZMod 5} (h : a * d - b * c ≠ 0) : lead a c ≠ 0 := by
  unfold lead
  by_cases ha : a = 0
  · rw [if_pos ha]
    intro hc
    apply h
    rw [ha, hc]
    ring
  · rw [if_neg ha]
    exact ha

theorem lam_ne {a b c d : ZMod 5} (h : a * d - b * c ≠ 0) : lam a c ≠ 0 := by
  intro h0
  have := inv5_mul (lead a c) (lead_ne h)
  unfold lam at h0
  rw [h0, mul_zero] at this
  exact absurd this (by decide)

theorem det_mk {a b c d : ZMod 5} (h : a * d - b * c ≠ 0) :
    (lam a c * a) * (lam a c * d) - (lam a c * b) * (lam a c * c) ≠ 0 := by
  have e : (lam a c * a) * (lam a c * d) - (lam a c * b) * (lam a c * c)
      = (lam a c * lam a c) * (a * d - b * c) := by ring
  rw [e]
  exact zm_mul_ne _ _ (zm_mul_ne _ _ (lam_ne h) (lam_ne h)) h

theorem norm_mk {a b c d : ZMod 5} (h : a * d - b * c ≠ 0) :
    lam a c * a = 1 ∨ (lam a c * a = 0 ∧ lam a c * c = 1) := by
  by_cases ha : a = 0
  · right
    have hc : c ≠ 0 := by
      intro hc
      apply h
      rw [ha, hc]
      ring
    have hl : lead a c = c := by simp [lead, ha]
    refine ⟨by rw [ha, mul_zero], ?_⟩
    unfold lam
    rw [hl, mul_comm]
    exact inv5_mul c hc
  · left
    have hl : lead a c = a := by simp [lead, ha]
    unfold lam
    rw [hl, mul_comm]
    exact inv5_mul a ha

/-- Elements of `PGL(2, 5)`: a matrix of nonzero determinant, normalised as above. -/
@[ext]
structure Grp where
  a : ZMod 5
  b : ZMod 5
  c : ZMod 5
  d : ZMod 5
  det : a * d - b * c ≠ 0
  norm : a = 1 ∨ (a = 0 ∧ c = 1)
  deriving DecidableEq

/-- The normalised class of the matrix `[[a, b], [c, d]]`, for a matrix of nonzero determinant. -/
def mk (a b c d : ZMod 5) (h : a * d - b * c ≠ 0) : Grp :=
  ⟨lam a c * a, lam a c * b, lam a c * c, lam a c * d, det_mk h, norm_mk h⟩

/-- The class of the matrix `[[a, b], [c, d]]` when its determinant is nonzero, else the identity. -/
def gZ (a b c d : ZMod 5) : Grp :=
  if h : a * d - b * c ≠ 0 then mk a b c d h else mk 1 0 0 1 (by decide)

theorem scale_det {a b c d μ : ZMod 5} (hμ : μ ≠ 0) (h : a * d - b * c ≠ 0) :
    (μ * a) * (μ * d) - (μ * b) * (μ * c) ≠ 0 := by
  have e : (μ * a) * (μ * d) - (μ * b) * (μ * c) = (μ * μ) * (a * d - b * c) := by ring
  rw [e]
  exact zm_mul_ne _ _ (zm_mul_ne _ _ hμ hμ) h

theorem lead_scale {a c μ : ZMod 5} (hμ : μ ≠ 0) : lead (μ * a) (μ * c) = μ * lead a c := by
  unfold lead
  by_cases ha : a = 0
  · simp [ha]
  · have ha' : μ * a ≠ 0 := zm_mul_ne _ _ hμ ha
    simp [ha, ha']

theorem lam_scale {a c μ : ZMod 5} (hμ : μ ≠ 0) (hL : lead a c ≠ 0) :
    lam (μ * a) (μ * c) = inv5 μ * lam a c := by
  unfold lam
  rw [lead_scale hμ, inv5_mul2 μ (lead a c) hμ hL]

theorem mk_scale {a b c d μ : ZMod 5} (hμ : μ ≠ 0) (h : a * d - b * c ≠ 0) :
    mk (μ * a) (μ * b) (μ * c) (μ * d) (scale_det hμ h) = mk a b c d h := by
  have hl : lam (μ * a) (μ * c) = inv5 μ * lam a c := lam_scale hμ (lead_ne h)
  have hi : inv5 μ * μ = 1 := by
    rw [mul_comm]
    exact inv5_mul μ hμ
  apply Grp.ext
  · show lam (μ * a) (μ * c) * (μ * a) = lam a c * a
    rw [hl]
    linear_combination (lam a c * a) * hi
  · show lam (μ * a) (μ * c) * (μ * b) = lam a c * b
    rw [hl]
    linear_combination (lam a c * b) * hi
  · show lam (μ * a) (μ * c) * (μ * c) = lam a c * c
    rw [hl]
    linear_combination (lam a c * c) * hi
  · show lam (μ * a) (μ * c) * (μ * d) = lam a c * d
    rw [hl]
    linear_combination (lam a c * d) * hi

theorem mk_congr {a b c d a' b' c' d' μ : ZMod 5} (hμ : μ ≠ 0) (h : a * d - b * c ≠ 0)
    (h' : a' * d' - b' * c' ≠ 0) (ha : a' = μ * a) (hb : b' = μ * b) (hc : c' = μ * c) (hd : d' = μ * d) :
    mk a' b' c' d' h' = mk a b c d h := by
  subst ha hb hc hd
  exact mk_scale hμ h

theorem mk_ext' {a b c d a' b' c' d' : ZMod 5} (h : a * d - b * c ≠ 0) (h' : a' * d' - b' * c' ≠ 0)
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') : mk a b c d h = mk a' b' c' d' h' := by
  subst ha hb hc hd
  rfl

theorem lam_normal {a c : ZMod 5} (h : a = 1 ∨ (a = 0 ∧ c = 1)) : lam a c = 1 := by
  rcases h with h | ⟨h1, h2⟩
  · have ha0 : a ≠ 0 := by
      rw [h]
      decide
    unfold lam lead
    rw [if_neg ha0, h]
    exact inv5_one
  · unfold lam lead
    rw [if_pos h1, h2]
    exact inv5_one

theorem mk_normal (g : Grp) : mk g.a g.b g.c g.d g.det = g := by
  have hl := lam_normal g.norm
  apply Grp.ext
  · show lam g.a g.c * g.a = g.a
    rw [hl, one_mul]
  · show lam g.a g.c * g.b = g.b
    rw [hl, one_mul]
  · show lam g.a g.c * g.c = g.c
    rw [hl, one_mul]
  · show lam g.a g.c * g.d = g.d
    rw [hl, one_mul]

theorem mul_det {a b c d a' b' c' d' : ZMod 5} (h : a * d - b * c ≠ 0) (h' : a' * d' - b' * c' ≠ 0) :
    (a * a' + b * c') * (c * b' + d * d') - (a * b' + b * d') * (c * a' + d * c') ≠ 0 := by
  have e : (a * a' + b * c') * (c * b' + d * d') - (a * b' + b * d') * (c * a' + d * c')
      = (a * d - b * c) * (a' * d' - b' * c') := by ring
  rw [e]
  exact zm_mul_ne _ _ h h'

theorem inv_det {a b c d : ZMod 5} (h : a * d - b * c ≠ 0) : d * a - (-b) * (-c) ≠ 0 := by
  have e : d * a - (-b) * (-c) = a * d - b * c := by ring
  rw [e]
  exact h

instance : Mul Grp :=
  ⟨fun g h => mk (g.a * h.a + g.b * h.c) (g.a * h.b + g.b * h.d) (g.c * h.a + g.d * h.c)
    (g.c * h.b + g.d * h.d) (mul_det g.det h.det)⟩

instance : Inv Grp :=
  ⟨fun g => mk g.d (-g.b) (-g.c) g.a (inv_det g.det)⟩

instance : One Grp :=
  ⟨mk 1 0 0 1 (by decide)⟩

/-- A group element `P` is a nonzero multiple of the matrix `(a, b, c, d)`. -/
def Scal (P : Grp) (a b c d : ZMod 5) : Prop :=
  ∃ μ : ZMod 5, μ ≠ 0 ∧ P.a = μ * a ∧ P.b = μ * b ∧ P.c = μ * c ∧ P.d = μ * d

theorem scal_of_mk {a b c d : ZMod 5} (h : a * d - b * c ≠ 0) : Scal (mk a b c d h) a b c d :=
  ⟨lam a c, lam_ne h, rfl, rfl, rfl, rfl⟩

theorem scal_mul_right (P k : Grp) (a b c d : ZMod 5) (hP : Scal P a b c d) (hdet : a * d - b * c ≠ 0) :
    P * k = mk (a * k.a + b * k.c) (a * k.b + b * k.d) (c * k.a + d * k.c) (c * k.b + d * k.d)
      (mul_det hdet k.det) := by
  obtain ⟨μ, hμ, p1, p2, p3, p4⟩ := hP
  exact mk_congr hμ (mul_det hdet k.det) _ (by rw [p1, p2]; ring) (by rw [p1, p2]; ring)
    (by rw [p3, p4]; ring) (by rw [p3, p4]; ring)

theorem mul_scal_left (g P : Grp) (a b c d : ZMod 5) (hP : Scal P a b c d) (hdet : a * d - b * c ≠ 0) :
    g * P = mk (g.a * a + g.b * c) (g.a * b + g.b * d) (g.c * a + g.d * c) (g.c * b + g.d * d)
      (mul_det g.det hdet) := by
  obtain ⟨μ, hμ, p1, p2, p3, p4⟩ := hP
  exact mk_congr hμ (mul_det g.det hdet) _ (by rw [p1, p3]; ring) (by rw [p2, p4]; ring)
    (by rw [p1, p3]; ring) (by rw [p2, p4]; ring)

theorem mul_assoc' (g h k : Grp) : g * h * k = g * (h * k) := by
  have hgh : Scal (g * h) (g.a * h.a + g.b * h.c) (g.a * h.b + g.b * h.d) (g.c * h.a + g.d * h.c)
      (g.c * h.b + g.d * h.d) := scal_of_mk (mul_det g.det h.det)
  have hhk : Scal (h * k) (h.a * k.a + h.b * k.c) (h.a * k.b + h.b * k.d) (h.c * k.a + h.d * k.c)
      (h.c * k.b + h.d * k.d) := scal_of_mk (mul_det h.det k.det)
  rw [scal_mul_right (g * h) k _ _ _ _ hgh (mul_det g.det h.det),
    mul_scal_left g (h * k) _ _ _ _ hhk (mul_det h.det k.det)]
  exact mk_ext' _ _ (by ring) (by ring) (by ring) (by ring)

theorem one_mul' (g : Grp) : 1 * g = g := by
  have h1 : Scal (1 : Grp) 1 0 0 1 := scal_of_mk (by decide)
  rw [scal_mul_right 1 g 1 0 0 1 h1 (by decide)]
  exact (mk_ext' _ _ (by ring) (by ring) (by ring) (by ring)).trans (mk_normal g)

theorem mul_one' (g : Grp) : g * 1 = g := by
  have h1 : Scal (1 : Grp) 1 0 0 1 := scal_of_mk (by decide)
  rw [mul_scal_left g 1 1 0 0 1 h1 (by decide)]
  exact (mk_ext' _ _ (by ring) (by ring) (by ring) (by ring)).trans (mk_normal g)

theorem inv_mul_cancel' (g : Grp) : g⁻¹ * g = 1 := by
  have hS : Scal (g⁻¹) g.d (-g.b) (-g.c) g.a := scal_of_mk (inv_det g.det)
  rw [scal_mul_right g⁻¹ g _ _ _ _ hS (inv_det g.det)]
  exact (mk_ext' _ _ (by ring) (by ring) (by ring) (by ring)).trans
    (mk_scale (μ := g.a * g.d - g.b * g.c) (a := 1) (b := 0) (c := 0) (d := 1) g.det (by decide))

instance : Group Grp where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  inv_mul_cancel := inv_mul_cancel'

/-! ### The numbering -/

/-- The Nat-level entries `(a, b, c, d)` of the class with index `n`. -/
def quadN (n : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  if n < 100 then
    (1, (n / 4) % 5, (n / 4) / 5, ((n / 4) % 5 * ((n / 4) / 5) + 1 + n % 4) % 5)
  else
    (0, (n - 100) / 5 + 1, 1, (n - 100) % 5)

/-- The group element with Nat entries `M`, for `M` of nonzero determinant. -/
def gM (M : ℕ × ℕ × ℕ × ℕ) : Grp :=
  gZ (M.1 : ZMod 5) (M.2.1 : ZMod 5) (M.2.2.1 : ZMod 5) (M.2.2.2 : ZMod 5)

/-- The element with index `n` (for `n < 120`). -/
def grpOf (n : ℕ) : Grp := gM (quadN n)

/-- The index of the class `[[a, b], [c, d]]`, for a normalised class. -/
def enc (a b c d : ZMod 5) : ℕ :=
  if a = 1 then (c.val * 5 + b.val) * 4 + (d - b * c - 1).val else 100 + (b.val - 1) * 5 + d.val

theorem k_lt : ∀ x : ZMod 5, x ≠ -1 → x.val < 4 := by
  decide

theorem nonzero_succ : ∀ k : ℕ, k < 4 → ((k : ZMod 5) + 1) ≠ 0 := by
  decide

theorem nonzero_pos : ∀ k : ℕ, k < 5 → 1 ≤ k → (k : ZMod 5) ≠ 0 := by
  decide

theorem gZ_entries {a b c d : ZMod 5} (h : a * d - b * c ≠ 0) (hn : a = 1 ∨ (a = 0 ∧ c = 1)) :
    (gZ a b c d).a = a ∧ (gZ a b c d).b = b ∧ (gZ a b c d).c = c ∧ (gZ a b c d).d = d := by
  have hg : gZ a b c d = mk a b c d h := by
    unfold gZ
    rw [dif_pos h]
  have hl := lam_normal hn
  rw [hg]
  refine ⟨by simp [mk, hl], by simp [mk, hl], by simp [mk, hl], by simp [mk, hl]⟩

theorem quadN_one (b c k : ℕ) (hb : b < 5) (hc : c < 5) (hk : k < 4) :
    quadN ((c * 5 + b) * 4 + k) = (1, b, c, (b * c + 1 + k) % 5) := by
  have hlt : (c * 5 + b) * 4 + k < 100 := by omega
  unfold quadN
  rw [if_pos hlt]
  have e1 : ((c * 5 + b) * 4 + k) / 4 = c * 5 + b := by omega
  have e2 : (c * 5 + b) % 5 = b := by omega
  have e3 : (c * 5 + b) / 5 = c := by omega
  have e4 : ((c * 5 + b) * 4 + k) % 4 = k := by omega
  rw [e1, e2, e3, e4]

theorem quadN_zero (b d : ℕ) (hb1 : 1 ≤ b) (hb : b < 5) (hd : d < 5) :
    quadN (100 + (b - 1) * 5 + d) = (0, b, 1, d) := by
  have hn : ¬ (100 + (b - 1) * 5 + d < 100) := by omega
  unfold quadN
  rw [if_neg hn]
  have e1 : (100 + (b - 1) * 5 + d - 100) / 5 = b - 1 := by omega
  have e2 : (100 + (b - 1) * 5 + d - 100) % 5 = d := by omega
  rw [e1, e2, show b - 1 + 1 = b by omega]

theorem val_k_lt (a b c d : ZMod 5) (h : a * d - b * c ≠ 0) (ha : a = 1) :
    (d - b * c - 1).val < 4 := by
  apply k_lt
  intro h'
  apply h
  rw [ha]
  linear_combination h'

theorem val0 : (0 : ZMod 5).val = 0 := rfl

theorem val1 : (1 : ZMod 5).val = 1 := rfl

theorem enc_lt (g : Grp) : enc g.a g.b g.c g.d < 120 := by
  have hb := ZMod.val_lt g.b
  have hc := ZMod.val_lt g.c
  have hd := ZMod.val_lt g.d
  rcases g.norm with h1 | ⟨h0, h1⟩
  · unfold enc
    rw [if_pos h1]
    have hk := val_k_lt g.a g.b g.c g.d g.det h1
    omega
  · unfold enc
    have hne : g.a ≠ 1 := by
      rw [h0]
      decide
    rw [if_neg hne]
    have hb0 : g.b ≠ 0 := by
      intro hb0
      apply g.det
      rw [h0, hb0]
      ring
    have hb1 : 1 ≤ g.b.val := Nat.one_le_iff_ne_zero.2 (fun h => hb0 ((ZMod.val_eq_zero g.b).1 h))
    omega

theorem quadN_enc (g : Grp) : quadN (enc g.a g.b g.c g.d) = (g.a.val, g.b.val, g.c.val, g.d.val) := by
  have hb := ZMod.val_lt g.b
  have hc := ZMod.val_lt g.c
  have hd := ZMod.val_lt g.d
  rcases g.norm with h1 | ⟨h0, h1⟩
  · have hk := val_k_lt g.a g.b g.c g.d g.det h1
    have hne : g.a = 1 := h1
    unfold enc
    rw [if_pos hne, quadN_one g.b.val g.c.val _ hb hc hk]
    have hb' : ((g.b.val : ℕ) : ZMod 5) = g.b := ZMod.natCast_zmod_val g.b
    have hc' : ((g.c.val : ℕ) : ZMod 5) = g.c := ZMod.natCast_zmod_val g.c
    have hk' : (((g.d - g.b * g.c - 1).val : ℕ) : ZMod 5) = g.d - g.b * g.c - 1 :=
      ZMod.natCast_zmod_val _
    have key : ((g.b.val * g.c.val + 1 + (g.d - g.b * g.c - 1).val : ℕ) : ZMod 5) = g.d := by
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_one, hb', hc', hk']
      ring
    rw [h1, val1]
    congr 1
    rw [← ZMod.val_natCast, key]
  · have hne : g.a ≠ 1 := by
      rw [h0]
      decide
    have hb0 : g.b ≠ 0 := by
      intro hb0
      apply g.det
      rw [h0, hb0]
      ring
    have hb1 : 1 ≤ g.b.val := Nat.one_le_iff_ne_zero.2 (fun h => hb0 ((ZMod.val_eq_zero g.b).1 h))
    unfold enc
    rw [if_neg hne, quadN_zero g.b.val g.d.val hb1 hb hd, h0, h1, val0, val1]

theorem grpOf_enc (g : Grp) : grpOf (enc g.a g.b g.c g.d) = g := by
  unfold grpOf gM
  rw [quadN_enc g]
  simp only [ZMod.natCast_zmod_val]
  unfold gZ
  rw [dif_pos g.det]
  exact mk_normal g

theorem quadN_det (n : ℕ) (hn : n < 120) :
    ((quadN n).1 : ZMod 5) * ((quadN n).2.2.2 : ZMod 5) - ((quadN n).2.1 : ZMod 5) * ((quadN n).2.2.1 : ZMod 5)
      ≠ 0 := by
  by_cases h : n < 100
  · obtain ⟨c, b, k, hb, hc, hk, rfl⟩ : ∃ c b k, b < 5 ∧ c < 5 ∧ k < 4 ∧ n = (c * 5 + b) * 4 + k :=
      ⟨n / 4 / 5, n / 4 % 5, n % 4, by omega, by omega, by omega, by omega⟩
    rw [quadN_one b c k hb hc hk]
    show ((1 : ℕ) : ZMod 5) * ((((b * c + 1 + k) % 5 : ℕ)) : ZMod 5) - ((b : ℕ) : ZMod 5) * ((c : ℕ) : ZMod 5)
      ≠ 0
    intro h0
    apply nonzero_succ k hk
    rw [ZMod.natCast_mod] at h0
    push_cast at h0
    linear_combination h0
  · obtain ⟨b, d, hb1, hb, hd, rfl⟩ : ∃ b d, 1 ≤ b ∧ b < 5 ∧ d < 5 ∧ n = 100 + (b - 1) * 5 + d :=
      ⟨(n - 100) / 5 + 1, (n - 100) % 5, by omega, by omega, by omega, by omega⟩
    rw [quadN_zero b d hb1 hb hd]
    show ((0 : ℕ) : ZMod 5) * ((d : ℕ) : ZMod 5) - ((b : ℕ) : ZMod 5) * ((1 : ℕ) : ZMod 5) ≠ 0
    intro h0
    apply nonzero_pos b hb hb1
    push_cast at h0
    linear_combination -h0

theorem quadN_norm (n : ℕ) :
    ((quadN n).1 : ZMod 5) = 1 ∨ (((quadN n).1 : ZMod 5) = 0 ∧ ((quadN n).2.2.1 : ZMod 5) = 1) := by
  unfold quadN
  split_ifs
  · left
    simp
  · right
    simp

theorem grpOf_entries (n : ℕ) (hn : n < 120) :
    (grpOf n).a = ((quadN n).1 : ZMod 5) ∧ (grpOf n).b = ((quadN n).2.1 : ZMod 5) ∧
      (grpOf n).c = ((quadN n).2.2.1 : ZMod 5) ∧ (grpOf n).d = ((quadN n).2.2.2 : ZMod 5) := by
  unfold grpOf gM
  exact gZ_entries (quadN_det n hn) (quadN_norm n)

theorem enc_grpOf {n : ℕ} (hn : n < 120) : enc (grpOf n).a (grpOf n).b (grpOf n).c (grpOf n).d = n := by
  obtain ⟨h1, h2, h3, h4⟩ := grpOf_entries n hn
  rw [h1, h2, h3, h4]
  have hv : ∀ x < 5, ((x : ℕ) : ZMod 5).val = x := fun x hx => by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hx]
  by_cases h : n < 100
  · obtain ⟨c, b, k, hb, hc, hk, rfl⟩ : ∃ c b k, b < 5 ∧ c < 5 ∧ k < 4 ∧ n = (c * 5 + b) * 4 + k :=
      ⟨n / 4 / 5, n / 4 % 5, n % 4, by omega, by omega, by omega, by omega⟩
    rw [quadN_one b c k hb hc hk]
    have hD : ((((b * c + 1 + k) % 5 : ℕ) : ZMod 5) - ((b : ℕ) : ZMod 5) * ((c : ℕ) : ZMod 5) - 1)
        = ((k : ℕ) : ZMod 5) := by
      rw [ZMod.natCast_mod]
      push_cast
      ring
    show enc ((1 : ℕ) : ZMod 5) ((b : ℕ) : ZMod 5) ((c : ℕ) : ZMod 5) ((((b * c + 1 + k) % 5 : ℕ)) : ZMod 5)
      = (c * 5 + b) * 4 + k
    unfold enc
    rw [if_pos Nat.cast_one, hv c hc, hv b hb, hD, hv k (by omega)]
  · obtain ⟨b, d, hb1, hb, hd, rfl⟩ : ∃ b d, 1 ≤ b ∧ b < 5 ∧ d < 5 ∧ n = 100 + (b - 1) * 5 + d :=
      ⟨(n - 100) / 5 + 1, (n - 100) % 5, by omega, by omega, by omega, by omega⟩
    rw [quadN_zero b d hb1 hb hd]
    have hv' : ∀ x < 5, ((x : ℕ) : ZMod 5).val = x := hv
    show enc ((0 : ℕ) : ZMod 5) ((b : ℕ) : ZMod 5) ((1 : ℕ) : ZMod 5) ((d : ℕ) : ZMod 5)
      = 100 + (b - 1) * 5 + d
    unfold enc
    have hne : ¬ (((0 : ℕ) : ZMod 5) = 1) := by
      rw [Nat.cast_zero]
      decide
    rw [if_neg hne, hv' b hb, hv' d hd]

/-- The numbering of `PGL(2, 5)`: `Grp ≃ Fin 120`. -/
def equiv120 : Grp ≃ Fin 120 where
  toFun g := ⟨enc g.a g.b g.c g.d, enc_lt g⟩
  invFun n := grpOf n.1
  left_inv g := grpOf_enc g
  right_inv n := by
    apply Fin.ext
    exact enc_grpOf n.2

end BipartiteDD.Haar.D5D7b.PGL5
