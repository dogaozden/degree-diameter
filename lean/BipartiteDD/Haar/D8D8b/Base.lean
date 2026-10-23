import BipartiteDD.Haar.D8D8b.PSL17
import Mathlib.Logic.Equiv.Fin.Basic

/-! The group `G = PSL(2, 17) × Z49` of the Δ8·D8 record (order 119952), and its numbering by `Fin 119952`. -/

namespace BipartiteDD.Haar.D8D8b

open BipartiteDD.Haar.PSL17

/-- The group `PSL(2, 17) × Z49`; the `Z49` factor is `Multiplicative (ZMod 49)`, so it adds. -/
abbrev G := PSL17.Grp × Multiplicative (ZMod 49)

/-- The index of `(p, z)` is `enc p * 49 + z`. -/
def idxG (g : G) : ℕ := enc g.1.a g.1.b g.1.c g.1.d * 49 + (Multiplicative.toAdd g.2).val

/-- The element with index `n`. -/
def gOf (n : ℕ) : G := (grpP (n / 49), Multiplicative.ofAdd ((n % 49 : ℕ) : ZMod 49))

theorem idxG_lt (g : G) : idxG g < 119952 := by
  have h1 := enc_lt g.1
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  unfold idxG
  omega

theorem gOf_idxG (g : G) : gOf (idxG g) = g := by
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  have h1 : (enc g.1.a g.1.b g.1.c g.1.d * 49 + (Multiplicative.toAdd g.2).val) / 49 =
      enc g.1.a g.1.b g.1.c g.1.d := by
    omega
  have h3 : (enc g.1.a g.1.b g.1.c g.1.d * 49 + (Multiplicative.toAdd g.2).val) % 49 =
      (Multiplicative.toAdd g.2).val := by
    omega
  unfold gOf idxG
  rw [h1, h3, grpP_enc, ZMod.natCast_zmod_val]
  rfl

theorem idxG_gOf (n : ℕ) (hn : n < 119952) : idxG (gOf n) = n := by
  have h1 : enc (grpP (n / 49)).a (grpP (n / 49)).b (grpP (n / 49)).c (grpP (n / 49)).d = n / 49 :=
    enc_grpP (n / 49) (by omega)
  have h2 : (Multiplicative.toAdd (Multiplicative.ofAdd ((n % 49 : ℕ) : ZMod 49))).val = n % 49 := by
    show (((n % 49 : ℕ) : ZMod 49)).val = n % 49
    rw [ZMod.val_natCast, Nat.mod_mod]
  unfold idxG gOf
  dsimp only
  rw [h1, h2]
  omega

/-- The numbering of `G` by `Fin 119952`. -/
def equivG : G ≃ Fin 119952 where
  toFun g := ⟨idxG g, idxG_lt g⟩
  invFun n := gOf n.1
  left_inv g := gOf_idxG g
  right_inv n := Fin.ext (idxG_gOf n.1 n.2)

/-- `G ⊕ G ≃ Fin 239904`: the two sides of the Haar graph. -/
def haarVert : G ⊕ G ≃ Fin 239904 :=
  (Equiv.sumCongr equivG equivG).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D8D8b
