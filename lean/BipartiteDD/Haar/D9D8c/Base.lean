import BipartiteDD.Haar.D7D8.PSL19
import Mathlib.Logic.Equiv.Fin.Basic

/-! The group `G = PSL(2, 19) × Z79` of the Δ9·D8 record (order 270180), and its numbering by `Fin 270180`. -/

namespace BipartiteDD.Haar.D9D8c

open BipartiteDD.Haar.PSL19

/-- The group `PSL(2, 19) × Z79`; the `Z79` factor is `Multiplicative (ZMod 79)`, so it adds. -/
abbrev G := PSL19.Grp × Multiplicative (ZMod 79)

/-- The index of `(p, z)` is `enc p * 79 + z`. -/
def idxG (g : G) : ℕ := enc g.1.a g.1.b g.1.c g.1.d * 79 + (Multiplicative.toAdd g.2).val

/-- The element with index `n`. -/
def gOf (n : ℕ) : G := (grpP (n / 79), Multiplicative.ofAdd ((n % 79 : ℕ) : ZMod 79))

theorem idxG_lt (g : G) : idxG g < 270180 := by
  have h1 := enc_lt g.1
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  unfold idxG
  omega

theorem gOf_idxG (g : G) : gOf (idxG g) = g := by
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  have h1 : (enc g.1.a g.1.b g.1.c g.1.d * 79 + (Multiplicative.toAdd g.2).val) / 79 =
      enc g.1.a g.1.b g.1.c g.1.d := by
    omega
  have h3 : (enc g.1.a g.1.b g.1.c g.1.d * 79 + (Multiplicative.toAdd g.2).val) % 79 =
      (Multiplicative.toAdd g.2).val := by
    omega
  unfold gOf idxG
  rw [h1, h3, grpP_enc, ZMod.natCast_zmod_val]
  rfl

theorem idxG_gOf (n : ℕ) (hn : n < 270180) : idxG (gOf n) = n := by
  have h1 : enc (grpP (n / 79)).a (grpP (n / 79)).b (grpP (n / 79)).c (grpP (n / 79)).d = n / 79 :=
    enc_grpP (n / 79) (by omega)
  have h2 : (Multiplicative.toAdd (Multiplicative.ofAdd ((n % 79 : ℕ) : ZMod 79))).val = n % 79 := by
    show (((n % 79 : ℕ) : ZMod 79)).val = n % 79
    rw [ZMod.val_natCast, Nat.mod_mod]
  unfold idxG gOf
  dsimp only
  rw [h1, h2]
  omega

/-- The numbering of `G` by `Fin 270180`. -/
def equivG : G ≃ Fin 270180 where
  toFun g := ⟨idxG g, idxG_lt g⟩
  invFun n := gOf n.1
  left_inv g := gOf_idxG g
  right_inv n := Fin.ext (idxG_gOf n.1 n.2)

/-- `G ⊕ G ≃ Fin 540360`: the two sides of the Haar graph. -/
def haarVert : G ⊕ G ≃ Fin 540360 :=
  (Equiv.sumCongr equivG equivG).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D9D8c
