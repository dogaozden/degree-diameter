import BipartiteDD.Haar.SL213
import Mathlib.Data.Fin.Basic

/-! The group `SL(2, 13) × Z_7` of order 15288, with a numbering `enc7 : G → ℕ` by `n < 15288`.

`Z_7` is written multiplicatively as `Multiplicative (ZMod 7)`, so the product is a `Group`.
The numbering is `n = 7 · SL213.enc (a, b, c, d) + z`. `grpOf7` is its inverse on `n < 15288`, and
`equiv30576` numbers the two sides of the Haar graph `G ⊕ G` by `Fin 30576`. -/

namespace BipartiteDD.Haar.SL213Z7

open BipartiteDD.Haar

/-- The group `SL(2, 13) × Z_7`. -/
abbrev Gp := SL213.Grp × Multiplicative (ZMod 7)

/-- The number of elements of `Gp`. -/
def order : ℕ := 15288

/-- The index of an element of `Gp`. -/
def enc7 (g : Gp) : ℕ := SL213.enc g.1.a g.1.b g.1.c g.1.d * 7 + (Multiplicative.toAdd g.2).val

/-- The element with index `n`, for `n < 15288`. -/
def grpOf7 (n : ℕ) : Gp :=
  (SL213.grpOf (n / 7), Multiplicative.ofAdd ((n % 7 : ℕ) : ZMod 7))

theorem enc7_lt (g : Gp) : enc7 g < 15288 := by
  have h1 := SL213.enc_lt g.1
  have h2 : (Multiplicative.toAdd g.2).val < 7 := ZMod.val_lt _
  unfold enc7
  omega

theorem grpOf7_enc (g : Gp) : grpOf7 (enc7 g) = g := by
  have h2 : (Multiplicative.toAdd g.2).val < 7 := ZMod.val_lt _
  have hd : (SL213.enc g.1.a g.1.b g.1.c g.1.d * 7 + (Multiplicative.toAdd g.2).val) / 7 =
      SL213.enc g.1.a g.1.b g.1.c g.1.d := by
    omega
  have hm : (SL213.enc g.1.a g.1.b g.1.c g.1.d * 7 + (Multiplicative.toAdd g.2).val) % 7 =
      (Multiplicative.toAdd g.2).val := by
    omega
  unfold grpOf7 enc7
  rw [hd, hm, SL213.grpOf_enc g.1, ZMod.natCast_zmod_val, ofAdd_toAdd]

theorem enc7_grpOf7 {n : ℕ} (hn : n < 15288) : enc7 (grpOf7 n) = n := by
  have hq : n / 7 < 2184 := by omega
  have h1 := SL213.enc_grpOf hq
  unfold enc7 grpOf7
  simp only [toAdd_ofAdd, ZMod.val_natCast]
  rw [h1]
  omega

/-- The numbering of the two sides of the Haar graph: `inl g` is `(g, A)`, `inr g` is `(g, B)`. -/
def equiv30576 : Gp ⊕ Gp ≃ Fin 30576 where
  toFun
    | .inl g => ⟨enc7 g, by have := enc7_lt g; omega⟩
    | .inr g => ⟨15288 + enc7 g, by have := enc7_lt g; omega⟩
  invFun n :=
    if h : n.val < 15288 then .inl (grpOf7 n.val) else .inr (grpOf7 (n.val - 15288))
  left_inv x := by
    rcases x with g | g
    · have := enc7_lt g
      simp only [dif_pos (show enc7 g < 15288 from this)]
      rw [grpOf7_enc]
    · have := enc7_lt g
      have h : ¬ (15288 + enc7 g < 15288) := by omega
      simp only [h, dif_neg, not_false_eq_true, Nat.add_sub_cancel_left]
      rw [grpOf7_enc]
  right_inv n := by
    apply Fin.ext
    by_cases h : n.val < 15288
    · simp only [h, dif_pos, enc7_grpOf7 h]
    · have hn : n.val - 15288 < 15288 := by omega
      simp only [h, dif_neg, not_false_eq_true]
      have := enc7_grpOf7 hn
      omega

end BipartiteDD.Haar.SL213Z7
