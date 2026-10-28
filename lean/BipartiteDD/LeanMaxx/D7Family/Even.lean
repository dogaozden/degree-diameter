import BipartiteDD.LeanMaxx.D7Family.Odd
import BipartiteDD.HexagonEven.Spread

/-! The infinite family at even `q` (research/theorems/D7_HEXAGON.md, Cor. 9.1).

`F` a finite field of characteristic `2`, `β ∈ F` with `t² + t + β² ≠ 0` for all `t` (it exists: `t ↦ t² + t` is
not injective, so not surjective, and every element is a square). The `q² + 1` points
`(1, x, 0, x + β y, (x + β y)² - x y, y, 0)` and `e₄` are the points of the elliptic quadric `Q⁻(3, q)` cut out by
`x₂ = x₆ = 0`, `x₃ = x₁ + β x₅` (there `Q = x₀x₄ + x₁² + x₁x₅ + β² x₅²`). For two of them
`B(u, v) = (Δx + β Δy)² - Δx Δy`, which is `Δx² + Δx Δy + β² Δy²` in characteristic `2`, nonzero unless `Δ = 0`.
The lines are `q² + 1` of the `q³ + 1` lines of the even Hermitian spread `SLineE d`, `d = β²`
(HexagonEven/Spread.lean). `d7_even` is `d7_of_sets` for these sets. -/

namespace BipartiteDD.LeanMaxx.D7Family

open SimpleGraph Finset BipartiteDD.Hexagon BipartiteDD.HexagonD7 BipartiteDD.HexagonD BipartiteDD.HexagonEven
open scoped Classical

variable {F : Type*} [Field F]

/-- The affine points of the even elliptic quadric. -/
def vqE (β x y : F) : V7 F := ![1, x, 0, x + β * y, (x + β * y) ^ 2 - x * y, y, 0]

theorem Qf_vqE (β x y : F) : Qf (vqE β x y) = 0 := by simp [Qf, vqE]

theorem vqE_ne_zero (β x y : F) : vqE β x y ≠ 0 := fun h => by
  have := congrFun h 0
  simp [vqE] at this

theorem Bf_vqE (β x y x' y' : F) :
    Bf (vqE β x y) (vqE β x' y') = ((x - x') + β * (y - y')) ^ 2 - (x - x') * (y - y') := by
  simp [Bf, vqE]; ring

theorem Bf_vqE_vinf (β x y : F) : Bf (vqE β x y) vinf = 1 := by simp [Bf, vqE, vinf]

theorem Bf_vinf_vqE (β x y : F) : Bf vinf (vqE β x y) = 1 := by simp [Bf, vqE, vinf]

section
variable {β : F} (hchar : (2 : F) = 0) (hβ : ∀ t : F, t ^ 2 + t + β ^ 2 ≠ 0)
include hchar hβ

theorem Bf_vqE_ne {x y x' y' : F} (hne : (x, y) ≠ (x', y')) : Bf (vqE β x y) (vqE β x' y') ≠ 0 := by
  rw [Bf_vqE]
  intro h
  by_cases hy : y = y'
  · subst hy
    apply hne
    have h2 : (x - x') ^ 2 = 0 := by simpa using h
    rw [sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)]
  · have hy' : y - y' ≠ 0 := sub_ne_zero.2 hy
    apply hβ ((x - x') / (y - y'))
    field_simp
    linear_combination h + ((x - x') * (y - y') * (1 - β)) * hchar

end

def vecE (β : F) : QIdx F → V7 F
  | none => vinf
  | some (x, y) => vqE β x y

theorem vecE_ne_zero (β : F) (i : QIdx F) : vecE β i ≠ 0 := by
  cases i with
  | none => exact vinf_ne_zero
  | some p => exact vqE_ne_zero β p.1 p.2

theorem Qf_vecE (β : F) (i : QIdx F) : Qf (vecE β i) = 0 := by
  cases i with
  | none => exact Qf_vinf
  | some p => exact Qf_vqE β p.1 p.2

def qptE (β : F) (i : QIdx F) : SPt F := ptOf (vecE β i) (vecE_ne_zero β i) (Qf_vecE β i)

section
variable {β : F} (hchar : (2 : F) = 0) (hβ : ∀ t : F, t ^ 2 + t + β ^ 2 ≠ 0)
include hchar hβ

theorem bf_vecE_ne {i j : QIdx F} (hne : i ≠ j) : Bf (vecE β i) (vecE β j) ≠ 0 := by
  rcases i with _ | ⟨x, y⟩ <;> rcases j with _ | ⟨x', y'⟩
  · exact absurd rfl hne
  · simp [vecE, Bf_vinf_vqE]
  · simp [vecE, Bf_vqE_vinf]
  · exact Bf_vqE_ne hchar hβ (fun h => hne (by rw [h]))

theorem bf_qptE_ne {i j : QIdx F} (hne : i ≠ j) : Bf (qptE β i).1.rep (qptE β j).1.rep ≠ 0 :=
  fun h => bf_vecE_ne hchar hβ hne
    ((bf_ptOf (hv := vecE_ne_zero β i) (hw := vecE_ne_zero β j) (hqv := Qf_vecE β i)
      (hqw := Qf_vecE β j)).1 h)

theorem qptE_injective : Function.Injective (qptE β : QIdx F → SPt F) := by
  intro i j hij
  by_contra hne
  exact ptOf_ne (bf_vecE_ne hchar hβ hne) hij

end

section Main

variable [Fintype F]

/-- A field of characteristic `2` has `β` with `t² + t + β² ≠ 0` for every `t`. -/
theorem exists_beta (hchar : (2 : F) = 0) : ∃ β : F, ∀ t : F, t ^ 2 + t + β ^ 2 ≠ 0 := by
  have hnot : ¬ Function.Injective (fun t : F => t ^ 2 + t) := by
    intro hinj
    have h01 : (0 : F) ^ 2 + 0 = (1 : F) ^ 2 + 1 := by
      have : (1 : F) + 1 = 0 := by linear_combination hchar
      rw [one_pow, this]; simp
    exact zero_ne_one (hinj h01)
  have hns : ¬ Function.Surjective (fun t : F => t ^ 2 + t) := fun h =>
    hnot (Finite.injective_iff_surjective.2 h)
  simp only [Function.Surjective, not_forall, not_exists] at hns
  obtain ⟨d, hd⟩ := hns
  haveI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hchar
  obtain ⟨β, hβ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) d
  refine ⟨β, fun t ht => hd t ?_⟩
  have : d = β ^ 2 := by rw [hβ]; ring
  rw [this]
  linear_combination ht - β ^ 2 * hchar

/-- **The family at even `q`.** For every finite field `F` of characteristic `2` with `q = |F| ≥ 5`:
`n_b(q + 2, 7) ≥ 6 N(q) + 2 (q² + 1)`. -/
theorem d7_even (hchar : (2 : F) = 0) (hq : 5 ≤ Fintype.card F) :
    ∃ G : SimpleGraph (Fin (6 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) +
        2 * (Fintype.card F ^ 2 + 1))), IsBipartiteDegDiam G (Fintype.card F + 2) 7 := by
  obtain ⟨β, hβ⟩ := exists_beta hchar
  have hRc : ((univ : Finset (QIdx F)).image (qptE β)).card = Fintype.card F ^ 2 + 1 := by
    rw [card_image_of_injective _ (qptE_injective hchar hβ), card_univ, Fintype.card_option,
      Fintype.card_prod]
    ring
  have hR : ∀ r ∈ (univ : Finset (QIdx F)).image (qptE β), ∀ s ∈ (univ : Finset (QIdx F)).image (qptE β),
      r ≠ s → Bf r.1.rep s.1.rep ≠ 0 := by
    intro r hr s hs hne
    obtain ⟨i, -, rfl⟩ := mem_image.1 hr
    obtain ⟨j, -, rfl⟩ := mem_image.1 hs
    exact bf_qptE_ne hchar hβ (fun h => hne (by rw [h]))
  have hd : ∀ t : F, t ^ 2 + t + (β ^ 2) ≠ 0 := hβ
  let Sall : Finset (HLine F) := (univ : Finset (SLineE (β ^ 2))).image Subtype.val
  have hSall : Sall.card = Fintype.card F ^ 3 + 1 := by
    rw [card_image_of_injective _ Subtype.val_injective, card_univ, card_slineE hd hchar]
  obtain ⟨S, hSsub, hSc⟩ := Finset.exists_subset_card_eq (s := Sall) (n := Fintype.card F ^ 2 + 1)
    (by rw [hSall]; exact Nat.add_le_add_right (Nat.pow_le_pow_right (by omega) (by norm_num)) 1)
  have hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Opp (hexInc (F := F)) x y := by
    intro x hx y hy hne
    obtain ⟨s, -, rfl⟩ := mem_image.1 (hSsub hx)
    obtain ⟨s', -, rfl⟩ := mem_image.1 (hSsub hy)
    exact sline_oppE hd hchar (fun h => hne (by rw [h]))
  exact d7_of_sets hq _ S hRc hSc hR hS

end Main

end BipartiteDD.LeanMaxx.D7Family
