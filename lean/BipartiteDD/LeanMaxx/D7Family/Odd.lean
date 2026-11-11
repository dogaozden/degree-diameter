import BipartiteDD.LeanMaxx.D7Family.Assembly
import BipartiteDD.HexagonD.Spread

/-! The infinite family at odd `q` (research/theorems/D7_HEXAGON.md, Cor. 9.1).

For a finite field `F` of odd characteristic and `a ∈ F` a non-square, the `q² + 1` points
`(1, x, 0, y, y² - a x², a x, 0)` (`x, y ∈ F`) and `(0, 0, 0, 0, 1, 0, 0)` of `Q(6, q)` are the points of an elliptic
quadric `Q⁻(3, q)` (the section `x₂ = x₆ = 0`, `x₅ = a x₁`, on which `Q = x₀x₄ + a x₁² - x₃²`). Two of them have
`B(u, v) = (y - y')² - a (x - x')² ≠ 0`, so `Bf` never vanishes on distinct ones (a partial ovoid of `H(q)` by (F4)).
For the lines take `q² + 1` of the `q³ + 1` lines of the Hermitian spread `SLine c`, `c = -a` (HexagonD/Spread.lean).
`d7_odd` is `d7_of_sets` for these sets. -/

namespace BipartiteDD.LeanMaxx.D7Family

open SimpleGraph Finset BipartiteDD.Hexagon BipartiteDD.HexagonD7 BipartiteDD.HexagonD
open scoped Classical

variable {F : Type*} [Field F]

theorem Bf_smul_smul (c d : F) (x y : V7 F) : Bf (c • x) (d • y) = c * d * Bf x y := by
  simp only [Bf, Pi.smul_apply, smul_eq_mul]; ring

/-- The point of `H(q)` spanned by a nonzero singular vector. -/
def ptOf (v : V7 F) (hv : v ≠ 0) (hq : Qf v = 0) : SPt F :=
  ⟨Projectivization.mk F v hv, by
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F v hv
    rw [← ha, Units.smul_def, Qf_smul, hq, mul_zero]⟩

theorem bf_ptOf {v w : V7 F} {hv : v ≠ 0} {hw : w ≠ 0} {hqv : Qf v = 0} {hqw : Qf w = 0} :
    Bf (ptOf v hv hqv).1.rep (ptOf w hw hqw).1.rep = 0 ↔ Bf v w = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F v hv
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep F w hw
  have e : Bf (ptOf v hv hqv).1.rep (ptOf w hw hqw).1.rep = (a : F) * b * Bf v w := by
    rw [← Bf_smul_smul]
    rw [Units.smul_def] at ha hb
    exact congrArg₂ Bf ha.symm hb.symm
  rw [e]
  simp [a.ne_zero, b.ne_zero]

theorem Bf_self (x : V7 F) : Bf x x = 2 * Qf x := by
  simp only [Bf, Qf]; ring

theorem ptOf_ne {v w : V7 F} {hv : v ≠ 0} {hw : w ≠ 0} {hqv : Qf v = 0} {hqw : Qf w = 0}
    (h : Bf v w ≠ 0) : ptOf v hv hqv ≠ ptOf w hw hqw := by
  intro he
  apply h
  refine (bf_ptOf (hv := hv) (hw := hw) (hqv := hqv) (hqw := hqw)).1 ?_
  rw [← he, Bf_self, (ptOf v hv hqv).2, mul_zero]

/-! ### The elliptic quadric -/

/-- The affine points `(1, x, 0, y, y² - a x², a x, 0)`. -/
def vq (a x y : F) : V7 F := ![1, x, 0, y, y ^ 2 - a * x ^ 2, a * x, 0]

/-- The point at infinity `e₄`. -/
def vinf : V7 F := ![0, 0, 0, 0, 1, 0, 0]

theorem Qf_vq (a x y : F) : Qf (vq a x y) = 0 := by simp [Qf, vq]; ring

theorem Qf_vinf : Qf (vinf : V7 F) = 0 := by simp [Qf, vinf]

theorem vq_ne_zero (a x y : F) : vq a x y ≠ 0 := fun h => by
  have := congrFun h 0
  simp [vq] at this

theorem vinf_ne_zero : (vinf : V7 F) ≠ 0 := fun h => by
  have := congrFun h 4
  simp [vinf] at this

theorem Bf_vq (a x y x' y' : F) : Bf (vq a x y) (vq a x' y') = (y - y') ^ 2 - a * (x - x') ^ 2 := by
  simp [Bf, vq]; ring

theorem Bf_vq_vinf (a x y : F) : Bf (vq a x y) vinf = 1 := by simp [Bf, vq, vinf]

theorem Bf_vinf_vq (a x y : F) : Bf vinf (vq a x y) = 1 := by simp [Bf, vq, vinf]

theorem Bf_vinf_vinf : Bf (vinf : V7 F) vinf = 0 := by simp [Bf, vinf]

variable {a : F} (ha : ¬ IsSquare a)
include ha

theorem Bf_vq_ne {x y x' y' : F} (hne : (x, y) ≠ (x', y')) : Bf (vq a x y) (vq a x' y') ≠ 0 := by
  rw [Bf_vq]
  intro h
  by_cases hx : x = x'
  · subst hx
    apply hne
    have : (y - y') ^ 2 = 0 := by simpa using h
    have := pow_eq_zero_iff (two_ne_zero) |>.1 this
    rw [sub_eq_zero.1 this]
  · have hx' : x - x' ≠ 0 := sub_ne_zero.2 hx
    apply ha
    refine ⟨(y - y') / (x - x'), ?_⟩
    field_simp
    linear_combination (-1 : F) * h

omit ha

/-- Indices of the quadric: the affine points and the point at infinity. -/
abbrev QIdx (F : Type*) := Option (F × F)

def vec (a : F) : QIdx F → V7 F
  | none => vinf
  | some (x, y) => vq a x y

theorem vec_ne_zero (a : F) (i : QIdx F) : vec a i ≠ 0 := by
  cases i with
  | none => exact vinf_ne_zero
  | some p => exact vq_ne_zero a p.1 p.2

theorem Qf_vec (a : F) (i : QIdx F) : Qf (vec a i) = 0 := by
  cases i with
  | none => exact Qf_vinf
  | some p => exact Qf_vq a p.1 p.2

/-- The point of `H(q)` of index `i`. -/
def qpt (a : F) (i : QIdx F) : SPt F := ptOf (vec a i) (vec_ne_zero a i) (Qf_vec a i)

theorem bf_vec_ne (ha : ¬ IsSquare a) {i j : QIdx F} (hne : i ≠ j) : Bf (vec a i) (vec a j) ≠ 0 := by
  rcases i with _ | ⟨x, y⟩ <;> rcases j with _ | ⟨x', y'⟩
  · exact absurd rfl hne
  · simp [vec, Bf_vinf_vq]
  · simp [vec, Bf_vq_vinf]
  · exact Bf_vq_ne ha (fun h => hne (by rw [h]))

theorem bf_qpt_ne (ha : ¬ IsSquare a) {i j : QIdx F} (hne : i ≠ j) :
    Bf (qpt a i).1.rep (qpt a j).1.rep ≠ 0 := fun h => bf_vec_ne ha hne ((bf_ptOf (hv := vec_ne_zero a i) (hw := vec_ne_zero a j) (hqv := Qf_vec a i) (hqw := Qf_vec a j)).1 h)

theorem qpt_injective (ha : ¬ IsSquare a) : Function.Injective (qpt a : QIdx F → SPt F) := by
  intro i j hij
  by_contra hne
  exact ptOf_ne (bf_vec_ne ha hne) hij


section Main

variable [Fintype F] [NeZero (2 : F)]

theorem ringChar_ne_two : ringChar F ≠ 2 := by
  intro h
  have h2 : (2 : F) = 0 := by
    have := (ringChar.eq_iff.1 h)
    exact_mod_cast CharP.cast_eq_zero F 2
  exact two_ne_zero h2

/-- **The family at odd `q`.** For every finite field `F` of odd characteristic with `q = |F| ≥ 5`:
`n_b(q + 2, 7) ≥ 6 N(q) + 2 (q² + 1)` with `N(q) = (q + 1)(1 + q² + q⁴)`. -/
theorem d7_odd (hq : 5 ≤ Fintype.card F) :
    ∃ G : SimpleGraph (Fin (6 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) +
        2 * (Fintype.card F ^ 2 + 1))), IsBipartiteDegDiam G (Fintype.card F + 2) 7 := by
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := F) ringChar_ne_two
  -- the points
  have hRc : ((univ : Finset (QIdx F)).image (qpt a)).card = Fintype.card F ^ 2 + 1 := by
    rw [card_image_of_injective _ (qpt_injective ha), card_univ, Fintype.card_option, Fintype.card_prod]
    ring
  have hR : ∀ r ∈ (univ : Finset (QIdx F)).image (qpt a), ∀ s ∈ (univ : Finset (QIdx F)).image (qpt a),
      r ≠ s → Bf r.1.rep s.1.rep ≠ 0 := by
    intro r hr s hs hne
    obtain ⟨i, -, rfl⟩ := mem_image.1 hr
    obtain ⟨j, -, rfl⟩ := mem_image.1 hs
    exact bf_qpt_ne ha (fun h => hne (by rw [h]))
  -- the lines
  have hc : ¬ IsSquare (-(-a)) := by rwa [neg_neg]
  let Sall : Finset (HLine F) := (univ : Finset (SLine (-a))).image Subtype.val
  have hSall : Sall.card = Fintype.card F ^ 3 + 1 := by
    rw [card_image_of_injective _ Subtype.val_injective, card_univ, card_sline hc]
  obtain ⟨S, hSsub, hSc⟩ := Finset.exists_subset_card_eq (s := Sall) (n := Fintype.card F ^ 2 + 1)
    (by rw [hSall]; exact Nat.add_le_add_right (Nat.pow_le_pow_right (by omega) (by norm_num)) 1)
  have hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Opp (hexInc (F := F)) x y := by
    intro x hx y hy hne
    obtain ⟨s, -, rfl⟩ := mem_image.1 (hSsub hx)
    obtain ⟨s', -, rfl⟩ := mem_image.1 (hSsub hy)
    exact sline_opp hc (fun h => hne (by rw [h]))
  exact d7_of_sets hq _ S hRc hSc hR hS

end Main

end BipartiteDD.LeanMaxx.D7Family
