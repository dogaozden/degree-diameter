import BipartiteDD.Haar.D7D8.PSL19
import Mathlib.Logic.Equiv.Fin.Basic

/-! The group `G = PSL(2, 19) × Z13` of the Δ7·D8 record (order 44460), and its numbering by `Fin 44460`. -/

namespace BipartiteDD.Haar.D7D8

open BipartiteDD.Haar.PSL19

/-- The group `PSL(2, 19) × Z13`. -/
abbrev G := PSL19.Grp × ZMod 13

/-- The index of `(p, z)` is `enc p * 13 + z`. -/
def idxG (g : G) : ℕ := enc g.1.a g.1.b g.1.c g.1.d * 13 + g.2.val

/-- The element with index `n`. -/
def gOf (n : ℕ) : G := (grpP (n / 13), ((n % 13 : ℕ) : ZMod 13))

theorem idxG_lt (g : G) : idxG g < 44460 := by
  have h1 := enc_lt g.1
  have h2 := ZMod.val_lt g.2
  unfold idxG
  omega

theorem gOf_idxG (g : G) : gOf (idxG g) = g := by
  have h2 := ZMod.val_lt g.2
  have h1 : (enc g.1.a g.1.b g.1.c g.1.d * 13 + g.2.val) / 13 = enc g.1.a g.1.b g.1.c g.1.d := by
    omega
  have h3 : (enc g.1.a g.1.b g.1.c g.1.d * 13 + g.2.val) % 13 = g.2.val := by
    omega
  unfold gOf idxG
  rw [h1, h3, grpP_enc, ZMod.natCast_zmod_val]

theorem idxG_gOf (n : ℕ) (hn : n < 44460) : idxG (gOf n) = n := by
  have h1 : enc (grpP (n / 13)).a (grpP (n / 13)).b (grpP (n / 13)).c (grpP (n / 13)).d = n / 13 :=
    enc_grpP (n / 13) (by omega)
  have h2 : (((n % 13 : ℕ) : ZMod 13)).val = n % 13 := by
    rw [ZMod.val_natCast, Nat.mod_mod]
  unfold idxG gOf
  dsimp only
  rw [h1, h2]
  omega

/-- The numbering of `G` by `Fin 44460`. -/
def equivG : G ≃ Fin 44460 where
  toFun g := ⟨idxG g, idxG_lt g⟩
  invFun n := gOf n.1
  left_inv g := gOf_idxG g
  right_inv n := Fin.ext (idxG_gOf n.1 n.2)

/-- `G ⊕ G ≃ Fin 88920`: the two sides of the Haar graph. -/
def haarVert : G ⊕ G ≃ Fin 88920 :=
  (Equiv.sumCongr equivG equivG).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D7D8
