import BipartiteDD.Haar.D7D9b.PSL29
import Mathlib.Logic.Equiv.Fin.Basic

/-! The group `G = PSL(2, 29) × Z19` of the Δ7·D9 record `462,840` (order 231420), and its numbering by `Fin 231420`. -/

namespace BipartiteDD.Haar.D7D9b

open BipartiteDD.Haar.PSL29

/-- The group `PSL(2, 29) × Z19`; the `Z19` factor is `Multiplicative (ZMod 19)`, so it adds. -/
abbrev G := PSL29.Grp × Multiplicative (ZMod 19)

/-- The index of `(p, z)` is `enc p * 19 + z`. -/
def idxG (g : G) : ℕ := enc g.1.a g.1.b g.1.c g.1.d * 19 + (Multiplicative.toAdd g.2).val

/-- The element with index `n`. -/
def gOf (n : ℕ) : G := (grpP (n / 19), Multiplicative.ofAdd ((n % 19 : ℕ) : ZMod 19))

theorem idxG_lt (g : G) : idxG g < 231420 := by
  have h1 := enc_lt g.1
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  unfold idxG
  omega

theorem gOf_idxG (g : G) : gOf (idxG g) = g := by
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  have h1 : (enc g.1.a g.1.b g.1.c g.1.d * 19 + (Multiplicative.toAdd g.2).val) / 19 =
      enc g.1.a g.1.b g.1.c g.1.d := by
    omega
  have h3 : (enc g.1.a g.1.b g.1.c g.1.d * 19 + (Multiplicative.toAdd g.2).val) % 19 =
      (Multiplicative.toAdd g.2).val := by
    omega
  unfold gOf idxG
  rw [h1, h3, grpP_enc, ZMod.natCast_zmod_val]
  rfl

theorem idxG_gOf (n : ℕ) (hn : n < 231420) : idxG (gOf n) = n := by
  have h1 : enc (grpP (n / 19)).a (grpP (n / 19)).b (grpP (n / 19)).c (grpP (n / 19)).d = n / 19 :=
    enc_grpP (n / 19) (by omega)
  have h2 : (Multiplicative.toAdd (Multiplicative.ofAdd ((n % 19 : ℕ) : ZMod 19))).val = n % 19 := by
    show (((n % 19 : ℕ) : ZMod 19)).val = n % 19
    rw [ZMod.val_natCast, Nat.mod_mod]
  unfold idxG gOf
  dsimp only
  rw [h1, h2]
  omega

/-- The numbering of `G` by `Fin 231420`. -/
def equivG : G ≃ Fin 231420 where
  toFun g := ⟨idxG g, idxG_lt g⟩
  invFun n := gOf n.1
  left_inv g := gOf_idxG g
  right_inv n := Fin.ext (idxG_gOf n.1 n.2)

/-- `G ⊕ G ≃ Fin 462840`: the two sides of the Haar graph. -/
def haarVert : G ⊕ G ≃ Fin 462840 :=
  (Equiv.sumCongr equivG equivG).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D7D9b
