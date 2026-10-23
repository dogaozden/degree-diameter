import BipartiteDD.Haar.SL19

/-! The group `SL(2, 19) × Z_3` of order 20520, with a computable numbering by `Fin 20520`.

The `Z_3` factor is `Multiplicative (ZMod 3)`. The element with index `n` is `(grpOf (n / 3), n % 3)`,
and the index of `(g, z)` is `3 * enc g + z`, where `enc g` is the index of `g` in `SL19`. -/

namespace BipartiteDD.Haar.SL19Z3

/-- `SL(2, 19) × Z_3`. -/
abbrev Grp := SL19.Grp × Multiplicative (ZMod 3)

/-- The element with index `n`, for `n < 20520`. -/
def grpOf (n : ℕ) : Grp :=
  (SL19.grpOf (n / 3), Multiplicative.ofAdd ((n % 3 : ℕ) : ZMod 3))

/-- The index of `g = (M, z)`. -/
def enc (g : Grp) : ℕ :=
  3 * SL19.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val

theorem enc_lt (g : Grp) : enc g < 20520 := by
  have h1 := SL19.enc_lt g.1
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  unfold enc
  omega

theorem grpOf_enc (g : Grp) : grpOf (enc g) = g := by
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  have hdiv : (3 * SL19.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val) / 3
      = SL19.enc g.1.a g.1.b g.1.c g.1.d := by omega
  have hmod : (3 * SL19.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val) % 3
      = (Multiplicative.toAdd g.2).val := by omega
  unfold grpOf enc
  rw [hdiv, hmod, ZMod.natCast_val, ZMod.cast_id', id, SL19.grpOf_enc]
  simp

theorem enc_grpOf {n : ℕ} (hn : n < 20520) : enc (grpOf n) = n := by
  have hz : (((n % 3 : ℕ) : ZMod 3)).val = n % 3 := by
    rw [ZMod.val_natCast]
    exact Nat.mod_mod_of_dvd n (by norm_num)
  have hsl : SL19.enc (SL19.grpOf (n / 3)).a (SL19.grpOf (n / 3)).b (SL19.grpOf (n / 3)).c
      (SL19.grpOf (n / 3)).d = n / 3 := by
    obtain ⟨ha, hb, hc, hd⟩ := SL19.grpOf_fields (n := n / 3) (by omega)
    rw [ha, hb, hc, hd]
    exact SL19.enc_quad (n / 3) (by omega)
  have hval : (Multiplicative.toAdd (Multiplicative.ofAdd ((n % 3 : ℕ) : ZMod 3))).val = n % 3 := hz
  unfold enc grpOf
  simp only [hsl, hval]
  omega

/-- The numbering of `SL(2, 19) × Z_3`: `Grp ≃ Fin 20520`. -/
def equiv20520 : Grp ≃ Fin 20520 where
  toFun g := ⟨enc g, enc_lt g⟩
  invFun n := grpOf n.1
  left_inv g := grpOf_enc g
  right_inv n := by
    apply Fin.ext
    exact enc_grpOf n.2

end BipartiteDD.Haar.SL19Z3
