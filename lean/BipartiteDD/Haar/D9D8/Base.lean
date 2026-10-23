import BipartiteDD.Haar.D9D8.PSL23
import Mathlib.Logic.Equiv.Fin.Basic

/-! The group `G = PSL(2, 23) × Z41` of the Δ9·D8 record (order 248952), and its numbering by `Fin 248952`. -/

namespace BipartiteDD.Haar.D9D8

open BipartiteDD.Haar.PSL23

/-- The group `PSL(2, 23) × Z41`; the `Z41` factor is `Multiplicative (ZMod 41)`, so it adds. -/
abbrev G := PSL23.Grp × Multiplicative (ZMod 41)

/-- The index of `(p, z)` is `enc p * 41 + z`. -/
def idxG (g : G) : ℕ := enc g.1.a g.1.b g.1.c g.1.d * 41 + (Multiplicative.toAdd g.2).val

/-- The element with index `n`. -/
def gOf (n : ℕ) : G := (grpP (n / 41), Multiplicative.ofAdd ((n % 41 : ℕ) : ZMod 41))

theorem idxG_lt (g : G) : idxG g < 248952 := by
  have h1 := enc_lt g.1
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  unfold idxG
  omega

theorem gOf_idxG (g : G) : gOf (idxG g) = g := by
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  have h1 : (enc g.1.a g.1.b g.1.c g.1.d * 41 + (Multiplicative.toAdd g.2).val) / 41 =
      enc g.1.a g.1.b g.1.c g.1.d := by
    omega
  have h3 : (enc g.1.a g.1.b g.1.c g.1.d * 41 + (Multiplicative.toAdd g.2).val) % 41 =
      (Multiplicative.toAdd g.2).val := by
    omega
  unfold gOf idxG
  rw [h1, h3, grpP_enc, ZMod.natCast_zmod_val]
  rfl

theorem idxG_gOf (n : ℕ) (hn : n < 248952) : idxG (gOf n) = n := by
  have h1 : enc (grpP (n / 41)).a (grpP (n / 41)).b (grpP (n / 41)).c (grpP (n / 41)).d = n / 41 :=
    enc_grpP (n / 41) (by omega)
  have h2 : (Multiplicative.toAdd (Multiplicative.ofAdd ((n % 41 : ℕ) : ZMod 41))).val = n % 41 := by
    show (((n % 41 : ℕ) : ZMod 41)).val = n % 41
    rw [ZMod.val_natCast, Nat.mod_mod]
  unfold idxG gOf
  dsimp only
  rw [h1, h2]
  omega

/-- The numbering of `G` by `Fin 248952`. -/
def equivG : G ≃ Fin 248952 where
  toFun g := ⟨idxG g, idxG_lt g⟩
  invFun n := gOf n.1
  left_inv g := gOf_idxG g
  right_inv n := Fin.ext (idxG_gOf n.1 n.2)

/-- `G ⊕ G ≃ Fin 497904`: the two sides of the Haar graph. -/
def haarVert : G ⊕ G ≃ Fin 497904 :=
  (Equiv.sumCongr equivG equivG).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D9D8
