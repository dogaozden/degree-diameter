import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! The group `PSL(2, 11)` of order 660, with a computable numbering by `ℕ`.

An element is a matrix `[[a, b], [c, d]]` over `ZMod 11` of determinant `1`, taken modulo `±1`. Each class has
one representative with `posB a c`: `a` when `c = 0`, and `c` otherwise, lies in `{0, …, 5}`. The product is the
matrix product, normalised by `canon`, which negates the matrix when it is not the representative.

The numbering is `enc`/`quad`: the `c = 0` elements come first (`n = (a - 1) * 11 + b`, `a ∈ 1…5`), then the
`c ≠ 0` ones (`n = 55 + ((c - 1) * 11 + a) * 11 + d`, `c ∈ 1…5`), with `b` determined by the determinant. -/

namespace BipartiteDD.Haar.D6D8d.PSL11

/-- The sign test: `posB a c` says that the matrix with first column `(a, c)` is the chosen representative. -/
def posB (a c : ZMod 11) : Bool :=
  if c = 0 then decide (a.val ≤ 5) else decide (c.val ≤ 5)

theorem neg_val_aux : ∀ x : ZMod 11, x ≠ 0 → decide ((-x).val ≤ 5) = !decide (x.val ≤ 5) := by
  decide

theorem zmod11_zero_ne_one : (0 : ZMod 11) ≠ 1 := by decide

/-- Negating the first column flips the sign test, for a matrix of determinant `1`. -/
theorem posB_neg {a b c d : ZMod 11} (h : a * d - b * c = 1) : posB (-a) (-c) = !posB a c := by
  by_cases hc : c = 0
  · have ha : a ≠ 0 := by
      intro h0
      rw [h0, hc, zero_mul, mul_zero, sub_zero] at h
      exact zmod11_zero_ne_one h
    simp only [posB]
    rw [if_pos (neg_eq_zero.2 hc), if_pos hc]
    exact neg_val_aux a ha
  · have hc' : -c ≠ 0 := neg_ne_zero.2 hc
    simp only [posB]
    rw [if_neg hc', if_neg hc]
    exact neg_val_aux c hc

/-- Elements of `PSL(2, 11)`: a determinant-one matrix in its chosen representative. -/
@[ext]
structure Grp where
  a : ZMod 11
  b : ZMod 11
  c : ZMod 11
  d : ZMod 11
  det : a * d - b * c = 1
  pos : posB a c = true
  deriving DecidableEq

/-- The representative of the class of the matrix `[[a, b], [c, d]]`. -/
def canon (a b c d : ZMod 11) (h : a * d - b * c = 1) : Grp :=
  if hp : posB a c = true then ⟨a, b, c, d, h, hp⟩
  else ⟨-a, -b, -c, -d, by linear_combination h, by
    rw [posB_neg h]
    simpa using hp⟩

theorem canon_pm (a b c d : ZMod 11) (h : a * d - b * c = 1) :
    ((canon a b c d h).a = a ∧ (canon a b c d h).b = b ∧ (canon a b c d h).c = c ∧ (canon a b c d h).d = d) ∨
    ((canon a b c d h).a = -a ∧ (canon a b c d h).b = -b ∧ (canon a b c d h).c = -c ∧
      (canon a b c d h).d = -d) := by
  unfold canon
  split_ifs
  · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl, rfl, rfl⟩

/-- Matrices that agree up to sign have the same representative. -/
theorem canon_congr {a b c d a' b' c' d' : ZMod 11} (h : a * d - b * c = 1) (h' : a' * d' - b' * c' = 1)
    (H : (a' = a ∧ b' = b ∧ c' = c ∧ d' = d) ∨ (a' = -a ∧ b' = -b ∧ c' = -c ∧ d' = -d)) :
    canon a' b' c' d' h' = canon a b c d h := by
  rcases H with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · rfl
  · by_cases hp : posB a c = true
    · have hn : posB (-a) (-c) = false := by
        rw [posB_neg h]
        simp [hp]
      unfold canon
      rw [dif_neg (by simp [hn]), dif_pos hp]
      ext <;> simp
    · have hn : posB (-a) (-c) = true := by
        rw [posB_neg h]
        simpa using hp
      unfold canon
      rw [dif_pos hn, dif_neg hp]

theorem canon_eq_of (g : Grp) {a b c d : ZMod 11} (h : a * d - b * c = 1)
    (H : a = g.a ∧ b = g.b ∧ c = g.c ∧ d = g.d) : canon a b c d h = g := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := H
  unfold canon
  rw [dif_pos g.pos]

instance : Mul Grp :=
  ⟨fun g h => canon (g.a * h.a + g.b * h.c) (g.a * h.b + g.b * h.d) (g.c * h.a + g.d * h.c)
    (g.c * h.b + g.d * h.d) (by linear_combination (g.a * g.d - g.b * g.c) * h.det + g.det)⟩

theorem mul_def (g h : Grp) : g * h = canon (g.a * h.a + g.b * h.c) (g.a * h.b + g.b * h.d)
    (g.c * h.a + g.d * h.c) (g.c * h.b + g.d * h.d)
    (by linear_combination (g.a * g.d - g.b * g.c) * h.det + g.det) := rfl

instance : One Grp := ⟨⟨1, 0, 0, 1, by ring, by decide⟩⟩

instance : Inv Grp := ⟨fun g => canon g.d (-g.b) (-g.c) g.a (by linear_combination g.det)⟩

theorem inv_def (g : Grp) : g⁻¹ = canon g.d (-g.b) (-g.c) g.a (by linear_combination g.det) := rfl

theorem one_a : (1 : Grp).a = 1 := rfl
theorem one_b : (1 : Grp).b = 0 := rfl
theorem one_c : (1 : Grp).c = 0 := rfl
theorem one_d : (1 : Grp).d = 1 := rfl

theorem mul_pm (g h : Grp) :
    ((g * h).a = g.a * h.a + g.b * h.c ∧ (g * h).b = g.a * h.b + g.b * h.d ∧
      (g * h).c = g.c * h.a + g.d * h.c ∧ (g * h).d = g.c * h.b + g.d * h.d) ∨
    ((g * h).a = -(g.a * h.a + g.b * h.c) ∧ (g * h).b = -(g.a * h.b + g.b * h.d) ∧
      (g * h).c = -(g.c * h.a + g.d * h.c) ∧ (g * h).d = -(g.c * h.b + g.d * h.d)) := by
  rw [mul_def]
  exact canon_pm _ _ _ _ _

theorem inv_pm (g : Grp) :
    ((g⁻¹).a = g.d ∧ (g⁻¹).b = -g.b ∧ (g⁻¹).c = -g.c ∧ (g⁻¹).d = g.a) ∨
    ((g⁻¹).a = -g.d ∧ (g⁻¹).b = -(-g.b) ∧ (g⁻¹).c = -(-g.c) ∧ (g⁻¹).d = -g.a) := by
  rw [inv_def]
  exact canon_pm _ _ _ _ _

instance : Group Grp where
  mul_assoc g h k := by
    rcases mul_pm g h with ⟨p1, p2, p3, p4⟩ | ⟨p1, p2, p3, p4⟩ <;>
      rcases mul_pm h k with ⟨q1, q2, q3, q4⟩ | ⟨q1, q2, q3, q4⟩ <;>
      · rw [mul_def (g * h) k, mul_def g (h * k)]
        apply canon_congr
        rw [p1, p2, p3, p4, q1, q2, q3, q4]
        first
          | (refine Or.inl ⟨?_, ?_, ?_, ?_⟩ <;> ring1)
          | (refine Or.inr ⟨?_, ?_, ?_, ?_⟩ <;> ring1)
  one_mul g := by
    rw [mul_def]
    apply canon_eq_of g
    simp only [one_a, one_b, one_c, one_d]
    exact ⟨by ring, by ring, by ring, by ring⟩
  mul_one g := by
    rw [mul_def]
    apply canon_eq_of g
    simp only [one_a, one_b, one_c, one_d]
    exact ⟨by ring, by ring, by ring, by ring⟩
  inv_mul_cancel g := by
    rw [mul_def]
    refine (canon_congr (a := 1) (b := 0) (c := 0) (d := 1) (by ring) _ ?_).trans
      (canon_eq_of 1 (by ring) ⟨rfl, rfl, rfl, rfl⟩)
    rcases inv_pm g with ⟨i1, i2, i3, i4⟩ | ⟨i1, i2, i3, i4⟩ <;> rw [i1, i2, i3, i4]
    · refine Or.inl ⟨?_, ?_, ?_, ?_⟩
      · linear_combination g.det
      · ring1
      · ring1
      · linear_combination g.det
    · refine Or.inr ⟨?_, ?_, ?_, ?_⟩
      · linear_combination (-1 : ZMod 11) * g.det
      · ring1
      · ring1
      · linear_combination (-1 : ZMod 11) * g.det

/-! The numbering. The inverse table of `ZMod 11`, then the closed-form bijection with `Fin 660`. -/

/-- `invTab[x] = x⁻¹` in `ZMod 11`, for `x ≠ 0`. -/
def invTab : List (ZMod 11) := [0, 1, 6, 4, 3, 9, 2, 8, 7, 5, 10]

def inv11 (x : ZMod 11) : ZMod 11 := invTab.getD x.val 0

/-- The matrix entries `(a, b, c, d)` of the class with index `n`, for `n < 660`. -/
def quad (n : ℕ) : ZMod 11 × ZMod 11 × ZMod 11 × ZMod 11 :=
  if n < 55 then
    (((n / 11 + 1 : ℕ) : ZMod 11), ((n % 11 : ℕ) : ZMod 11), 0, inv11 ((n / 11 + 1 : ℕ) : ZMod 11))
  else
    let m := n - 55
    let c : ZMod 11 := ((m / 121 + 1 : ℕ) : ZMod 11)
    let a : ZMod 11 := ((m / 11 % 11 : ℕ) : ZMod 11)
    let d : ZMod 11 := ((m % 11 : ℕ) : ZMod 11)
    (a, (a * d - 1) * inv11 c, c, d)

/-- The index of the class of `[[a, b], [c, d]]`. -/
def enc (a b c d : ZMod 11) : ℕ :=
  if c = 0 then (a.val - 1) * 11 + b.val else 55 + ((c.val - 1) * 11 + a.val) * 11 + d.val

theorem val_cast {k : ℕ} (hk : k < 11) : ((k : ℕ) : ZMod 11).val = k := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]

theorem val_pos_of_ne {x : ZMod 11} (hx : x ≠ 0) : 1 ≤ x.val :=
  Nat.one_le_iff_ne_zero.2 (fun h0 => hx (ZMod.val_eq_zero x |>.1 h0))

theorem posB_c_zero {a : ZMod 11} (hp : posB a 0 = true) : a.val ≤ 5 := by
  simpa [posB] using hp

theorem posB_c_ne {c : ZMod 11} (hc : c ≠ 0) (hp : posB a c = true) : c.val ≤ 5 := by
  simpa [posB, hc] using hp

theorem inv11_mul : ∀ x : ZMod 11, x ≠ 0 → x * inv11 x = 1 := by
  decide

theorem inv11_eq : ∀ x y : ZMod 11, x * y = 1 → inv11 x = y := by
  decide

theorem enc_lt_of (a b c d : ZMod 11) (h : a * d - b * c = 1) (hp : posB a c = true) :
    enc a b c d < 660 := by
  unfold enc
  split_ifs with hc
  · have ha9 := posB_c_zero (hc ▸ hp)
    have ha1 : 1 ≤ a.val := val_pos_of_ne (by
      rintro rfl
      rw [hc, zero_mul, mul_zero, sub_zero] at h
      exact zmod11_zero_ne_one h)
    have hb := ZMod.val_lt b
    omega
  · have hc9 := posB_c_ne hc hp
    have hc1 := val_pos_of_ne hc
    have ha := ZMod.val_lt a
    have hd := ZMod.val_lt d
    omega

theorem quad_enc_of (a b c d : ZMod 11) (h : a * d - b * c = 1) (hp : posB a c = true) :
    quad (enc a b c d) = (a, b, c, d) := by
  by_cases hc : c = 0
  · subst hc
    have ha9 := posB_c_zero hp
    have ha1 : 1 ≤ a.val := val_pos_of_ne (by
      rintro rfl
      rw [zero_mul, mul_zero, sub_zero] at h
      exact zmod11_zero_ne_one h)
    have hb := ZMod.val_lt b
    have hen : enc a b 0 d = (a.val - 1) * 11 + b.val := by
      simp [enc]
    rw [hen]
    unfold quad
    rw [if_pos (by omega)]
    have e1 : ((a.val - 1) * 11 + b.val) / 11 + 1 = a.val := by omega
    have e2 : ((a.val - 1) * 11 + b.val) % 11 = b.val := by omega
    rw [e1, e2, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have hd : inv11 a = d := inv11_eq a d (by simpa using h)
    rw [hd]
  · have hc9 := posB_c_ne hc hp
    have hc1 := val_pos_of_ne hc
    have hen : enc a b c d = 55 + ((c.val - 1) * 11 + a.val) * 11 + d.val := by
      simp [enc, hc]
    have ha := ZMod.val_lt a
    have hd := ZMod.val_lt d
    rw [hen]
    unfold quad
    rw [if_neg (by omega)]
    dsimp only
    have e1 : (55 + ((c.val - 1) * 11 + a.val) * 11 + d.val - 55) / 121 + 1 = c.val := by omega
    have e2 : (55 + ((c.val - 1) * 11 + a.val) * 11 + d.val - 55) / 11 % 11 = a.val := by omega
    have e3 : (55 + ((c.val - 1) * 11 + a.val) * 11 + d.val - 55) % 11 = d.val := by omega
    rw [e1, e2, e3, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have hinv := inv11_mul c hc
    have hb : (a * d - 1) * inv11 c = b := by
      linear_combination (inv11 c) * h + b * hinv
    rw [hb]

set_option maxRecDepth 100000 in
theorem quad_valid : ∀ n < 660, (quad n).1 * (quad n).2.2.2 - (quad n).2.1 * (quad n).2.2.1 = 1 ∧
    posB (quad n).1 (quad n).2.2.1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem enc_of_quad : ∀ n < 660, enc (quad n).1 (quad n).2.1 (quad n).2.2.1 (quad n).2.2.2 = n := by
  decide +kernel

/-- The class with index `n`, for `n < 660`; the identity for other `n`. -/
def grpP (n : ℕ) : Grp :=
  if h : (quad n).1 * (quad n).2.2.2 - (quad n).2.1 * (quad n).2.2.1 = 1 ∧
      posB (quad n).1 (quad n).2.2.1 = true then
    ⟨(quad n).1, (quad n).2.1, (quad n).2.2.1, (quad n).2.2.2, h.1, h.2⟩
  else 1

theorem enc_lt (g : Grp) : enc g.a g.b g.c g.d < 660 :=
  enc_lt_of g.a g.b g.c g.d g.det g.pos

theorem grpP_enc (g : Grp) : grpP (enc g.a g.b g.c g.d) = g := by
  have hq := quad_enc_of g.a g.b g.c g.d g.det g.pos
  unfold grpP
  simp only [hq]
  rw [dif_pos ⟨g.det, g.pos⟩]

theorem enc_grpP (m : ℕ) (hm : m < 660) : enc (grpP m).a (grpP m).b (grpP m).c (grpP m).d = m := by
  have hv := quad_valid m hm
  have he := enc_of_quad m hm
  unfold grpP
  rw [dif_pos hv]
  exact he

end BipartiteDD.Haar.D6D8d.PSL11
