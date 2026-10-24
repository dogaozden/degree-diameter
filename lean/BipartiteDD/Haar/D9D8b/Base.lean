import BipartiteDD.Haar.D9D8b.SL2
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-! The group `G = SL(2, 27) × Z13` of the Δ9·D8 record (order 255528), and its numbering by `Fin 255528`. -/

namespace BipartiteDD.Haar.D9D8b

/-- The group `SL(2, 27) × Z13`; the `Z13` factor is `Multiplicative (ZMod 13)`, so it adds. -/
abbrev G := SL2 × Multiplicative (ZMod 13)

/-- The index of `(g, z)` is `enc g * 13 + z`. -/
def idxG (g : G) : ℕ := enc g.1 * 13 + (Multiplicative.toAdd g.2).val

/-- The element with index `n`. -/
def gOf (n : ℕ) : G := (grpP (n / 13), Multiplicative.ofAdd ((n % 13 : ℕ) : ZMod 13))

theorem idxG_lt (g : G) : idxG g < 255528 := by
  have h1 := enc_lt g.1
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  unfold idxG
  omega

theorem gOf_idxG (g : G) : gOf (idxG g) = g := by
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  have h1 : (enc g.1 * 13 + (Multiplicative.toAdd g.2).val) / 13 = enc g.1 := by
    omega
  have h3 : (enc g.1 * 13 + (Multiplicative.toAdd g.2).val) % 13 = (Multiplicative.toAdd g.2).val := by
    omega
  unfold gOf idxG
  rw [h1, h3, grpP_enc, ZMod.natCast_zmod_val]
  rfl

theorem idxG_gOf (n : ℕ) (hn : n < 255528) : idxG (gOf n) = n := by
  have h1 : enc (grpP (n / 13)) = n / 13 := enc_grpP (n / 13) (by omega)
  have h2 : (Multiplicative.toAdd (Multiplicative.ofAdd ((n % 13 : ℕ) : ZMod 13))).val = n % 13 := by
    show (((n % 13 : ℕ) : ZMod 13)).val = n % 13
    rw [ZMod.val_natCast, Nat.mod_mod]
  unfold idxG gOf
  dsimp only
  rw [h1, h2]
  omega

/-- The numbering of `G` by `Fin 255528`. -/
def equivG : G ≃ Fin 255528 where
  toFun g := ⟨idxG g, idxG_lt g⟩
  invFun n := gOf n.1
  left_inv g := gOf_idxG g
  right_inv n := Fin.ext (idxG_gOf n.1 n.2)

/-- `G ⊕ G ≃ Fin 511056`: the two sides of the Haar graph. -/
def haarVert : G ⊕ G ≃ Fin 511056 :=
  (Equiv.sumCongr equivG equivG).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D9D8b
