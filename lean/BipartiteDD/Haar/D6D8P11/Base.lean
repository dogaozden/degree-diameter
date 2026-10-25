import BipartiteDD.Haar.D6D8P11.PSL11
import Mathlib.Logic.Equiv.Fin.Basic

/-! The group `G = PSL(2, 11) × Z24` of the Δ6·D8 record (order 15840), and its numbering by `Fin 15840`. -/

namespace BipartiteDD.Haar.D6D8P11

open BipartiteDD.Haar.PSL11

/-- The group `PSL(2, 11) × Z24`; the `Z24` factor is `Multiplicative (ZMod 24)`, so it adds. -/
abbrev G := PSL11.Grp × Multiplicative (ZMod 24)

/-- The index of `(p, z)` is `enc p * 24 + z`. -/
def idxG (g : G) : ℕ := enc g.1.a g.1.b g.1.c g.1.d * 24 + (Multiplicative.toAdd g.2).val

/-- The element with index `n`. -/
def gOf (n : ℕ) : G := (grpP (n / 24), Multiplicative.ofAdd ((n % 24 : ℕ) : ZMod 24))

theorem idxG_lt (g : G) : idxG g < 15840 := by
  have h1 := enc_lt g.1
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  unfold idxG
  omega

theorem gOf_idxG (g : G) : gOf (idxG g) = g := by
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  have h1 : (enc g.1.a g.1.b g.1.c g.1.d * 24 + (Multiplicative.toAdd g.2).val) / 24 =
      enc g.1.a g.1.b g.1.c g.1.d := by
    omega
  have h3 : (enc g.1.a g.1.b g.1.c g.1.d * 24 + (Multiplicative.toAdd g.2).val) % 24 =
      (Multiplicative.toAdd g.2).val := by
    omega
  unfold gOf idxG
  rw [h1, h3, grpP_enc, ZMod.natCast_zmod_val]
  rfl

theorem idxG_gOf (n : ℕ) (hn : n < 15840) : idxG (gOf n) = n := by
  have h1 : enc (grpP (n / 24)).a (grpP (n / 24)).b (grpP (n / 24)).c (grpP (n / 24)).d = n / 24 :=
    enc_grpP (n / 24) (by omega)
  have h2 : (Multiplicative.toAdd (Multiplicative.ofAdd ((n % 24 : ℕ) : ZMod 24))).val = n % 24 := by
    show (((n % 24 : ℕ) : ZMod 24)).val = n % 24
    rw [ZMod.val_natCast, Nat.mod_mod]
  unfold idxG gOf
  dsimp only
  rw [h1, h2]
  omega

/-- The numbering of `G` by `Fin 15840`. -/
def equivG : G ≃ Fin 15840 where
  toFun g := ⟨idxG g, idxG_lt g⟩
  invFun n := gOf n.1
  left_inv g := gOf_idxG g
  right_inv n := Fin.ext (idxG_gOf n.1 n.2)

/-- `G ⊕ G ≃ Fin 31680`: the two sides of the Haar graph. -/
def haarVert : G ⊕ G ≃ Fin 31680 :=
  (Equiv.sumCongr equivG equivG).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D6D8P11
