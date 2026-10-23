import BipartiteDD.Haar.D8D7b.SL8
import Mathlib.Data.ZMod.Basic

/-! The group `SL(2, 8) × Z_43` of order 21672, with a computable numbering by `Fin 21672`.

The `Z_43` factor is `Multiplicative (ZMod 43)`. The element with index `n` is `(grpOf (n / 43), n % 43)`,
and the index of `(g, z)` is `43 * enc g + z`, where `enc g` is the index of `g` in `SL8`. -/

namespace BipartiteDD.Haar.D8D7b.SL8Z43

/-- `SL(2, 8) × Z_43`. -/
abbrev Grp := SL8.Grp × Multiplicative (ZMod 43)

/-- The element with index `n`, for `n < 21672`. -/
def grpOf (n : ℕ) : Grp :=
  (SL8.grpOf (n / 43), Multiplicative.ofAdd ((n % 43 : ℕ) : ZMod 43))

/-- The index of `g = (M, z)`. -/
def enc (g : Grp) : ℕ :=
  43 * SL8.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val

theorem enc_lt (g : Grp) : enc g < 21672 := by
  have h1 := SL8.enc_lt g.1.a g.1.b g.1.c g.1.d
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  unfold enc
  omega

theorem grpOf_enc (g : Grp) : grpOf (enc g) = g := by
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  have hdiv : (43 * SL8.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val) / 43
      = SL8.enc g.1.a g.1.b g.1.c g.1.d := by omega
  have hmod : (43 * SL8.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val) % 43
      = (Multiplicative.toAdd g.2).val := by omega
  unfold grpOf enc
  rw [hdiv, hmod, ZMod.natCast_val, ZMod.cast_id', id, SL8.grpOf_enc]
  simp

theorem enc_grpOf {n : ℕ} (hn : n < 21672) : enc (grpOf n) = n := by
  have hz : (((n % 43 : ℕ) : ZMod 43)).val = n % 43 := by
    rw [ZMod.val_natCast]
    exact Nat.mod_mod_of_dvd n (by norm_num)
  have hsl : SL8.enc (SL8.grpOf (n / 43)).a (SL8.grpOf (n / 43)).b (SL8.grpOf (n / 43)).c
      (SL8.grpOf (n / 43)).d = n / 43 := by
    obtain ⟨ha, hb, hc, hd⟩ := SL8.grpOf_fields (n := n / 43) (by omega)
    rw [ha, hb, hc, hd]
    exact SL8.enc_quad (n / 43) (by omega)
  have hval : (Multiplicative.toAdd (Multiplicative.ofAdd ((n % 43 : ℕ) : ZMod 43))).val = n % 43 := hz
  unfold enc grpOf
  simp only [hsl, hval]
  omega

/-- The numbering of `SL(2, 8) × Z_43`: `Grp ≃ Fin 21672`. -/
def equiv21672 : Grp ≃ Fin 21672 where
  toFun g := ⟨enc g, enc_lt g⟩
  invFun n := grpOf n.1
  left_inv g := grpOf_enc g
  right_inv n := by
    apply Fin.ext
    exact enc_grpOf n.2

end BipartiteDD.Haar.D8D7b.SL8Z43
