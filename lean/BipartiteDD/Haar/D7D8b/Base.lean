import BipartiteDD.Haar.D7D8.PSL19
import Mathlib.Logic.Equiv.Fin.Basic

/-! The group `G = PSL(2, 19) × Z14` of the Δ7·D8 record (order 47880), and its numbering by `Fin 47880`. -/

namespace BipartiteDD.Haar.D7D8b

open BipartiteDD.Haar.PSL19

/-- The group `PSL(2, 19) × Z14`; the `Z14` factor is `Multiplicative (ZMod 14)`, so it adds. -/
abbrev G := PSL19.Grp × Multiplicative (ZMod 14)

/-- The index of `(p, z)` is `enc p * 14 + z`. -/
def idxG (g : G) : ℕ := enc g.1.a g.1.b g.1.c g.1.d * 14 + (Multiplicative.toAdd g.2).val

/-- The element with index `n`. -/
def gOf (n : ℕ) : G := (grpP (n / 14), Multiplicative.ofAdd ((n % 14 : ℕ) : ZMod 14))

theorem idxG_lt (g : G) : idxG g < 47880 := by
  have h1 := enc_lt g.1
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  unfold idxG
  omega

theorem gOf_idxG (g : G) : gOf (idxG g) = g := by
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  have h1 : (enc g.1.a g.1.b g.1.c g.1.d * 14 + (Multiplicative.toAdd g.2).val) / 14 =
      enc g.1.a g.1.b g.1.c g.1.d := by
    omega
  have h3 : (enc g.1.a g.1.b g.1.c g.1.d * 14 + (Multiplicative.toAdd g.2).val) % 14 =
      (Multiplicative.toAdd g.2).val := by
    omega
  unfold gOf idxG
  rw [h1, h3, grpP_enc, ZMod.natCast_zmod_val]
  rfl

theorem idxG_gOf (n : ℕ) (hn : n < 47880) : idxG (gOf n) = n := by
  have h1 : enc (grpP (n / 14)).a (grpP (n / 14)).b (grpP (n / 14)).c (grpP (n / 14)).d = n / 14 :=
    enc_grpP (n / 14) (by omega)
  have h2 : (Multiplicative.toAdd (Multiplicative.ofAdd ((n % 14 : ℕ) : ZMod 14))).val = n % 14 := by
    show (((n % 14 : ℕ) : ZMod 14)).val = n % 14
    rw [ZMod.val_natCast, Nat.mod_mod]
  unfold idxG gOf
  dsimp only
  rw [h1, h2]
  omega

/-- The numbering of `G` by `Fin 47880`. -/
def equivG : G ≃ Fin 47880 where
  toFun g := ⟨idxG g, idxG_lt g⟩
  invFun n := gOf n.1
  left_inv g := gOf_idxG g
  right_inv n := Fin.ext (idxG_gOf n.1 n.2)

/-- `G ⊕ G ≃ Fin 95760`: the two sides of the Haar graph. -/
def haarVert : G ⊕ G ≃ Fin 95760 :=
  (Equiv.sumCongr equivG equivG).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D7D8b
