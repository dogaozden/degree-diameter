import BipartiteDD.Haar.SL31

/-! The group `SL(2, 31) × Z_7` of order 208320, with a computable numbering by `Fin 208320`.

The `Z_7` factor is `Multiplicative (ZMod 7)`. The element with index `n` is `(grpOf (n / 7), n % 7)`,
and the index of `(g, z)` is `7 * enc g + z`, where `enc g` is the index of `g` in `SL31`. -/

namespace BipartiteDD.Haar.SL31Z7

/-- `SL(2, 31) × Z_7`. -/
abbrev Grp := SL31.Grp × Multiplicative (ZMod 7)

/-- The element with index `n`, for `n < 208320`. -/
def grpOf (n : ℕ) : Grp :=
  (SL31.grpOf (n / 7), Multiplicative.ofAdd ((n % 7 : ℕ) : ZMod 7))

/-- The index of `g = (M, z)`. -/
def enc (g : Grp) : ℕ :=
  7 * SL31.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val

theorem enc_lt (g : Grp) : enc g < 208320 := by
  have h1 := SL31.enc_lt g.1
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  unfold enc
  omega

theorem grpOf_enc (g : Grp) : grpOf (enc g) = g := by
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  have hdiv : (7 * SL31.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val) / 7
      = SL31.enc g.1.a g.1.b g.1.c g.1.d := by omega
  have hmod : (7 * SL31.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val) % 7
      = (Multiplicative.toAdd g.2).val := by omega
  unfold grpOf enc
  rw [hdiv, hmod, ZMod.natCast_val, ZMod.cast_id', id, SL31.grpOf_enc]
  simp

theorem enc_grpOf {n : ℕ} (hn : n < 208320) : enc (grpOf n) = n := by
  have hz : (((n % 7 : ℕ) : ZMod 7)).val = n % 7 := by
    rw [ZMod.val_natCast]
    exact Nat.mod_mod_of_dvd n (by norm_num)
  have hsl : SL31.enc (SL31.grpOf (n / 7)).a (SL31.grpOf (n / 7)).b (SL31.grpOf (n / 7)).c
      (SL31.grpOf (n / 7)).d = n / 7 := by
    obtain ⟨ha, hb, hc, hd⟩ := SL31.grpOf_fields (n := n / 7) (by omega)
    rw [ha, hb, hc, hd]
    exact SL31.enc_quad (n / 7) (by omega)
  have hval : (Multiplicative.toAdd (Multiplicative.ofAdd ((n % 7 : ℕ) : ZMod 7))).val = n % 7 := hz
  unfold enc grpOf
  simp only [hsl, hval]
  omega

/-- The numbering of `SL(2, 31) × Z_7`: `Grp ≃ Fin 208320`. -/
def equiv208320 : Grp ≃ Fin 208320 where
  toFun g := ⟨enc g, enc_lt g⟩
  invFun n := grpOf n.1
  left_inv g := grpOf_enc g
  right_inv n := by
    apply Fin.ext
    exact enc_grpOf n.2

end BipartiteDD.Haar.SL31Z7
