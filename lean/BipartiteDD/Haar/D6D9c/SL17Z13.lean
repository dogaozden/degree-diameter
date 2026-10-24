import BipartiteDD.Haar.D6D9c.SL17

/-! The group `SL(2, 17) × Z_13` of order 63648, with a computable numbering by `Fin 63648`.

The `Z_13` factor is `Multiplicative (ZMod 13)`. The element with index `n` is `(grpOf (n / 13), n % 13)`,
and the index of `(g, z)` is `13 * enc g + z`, where `enc g` is the index of `g` in `SL17`. -/

namespace BipartiteDD.Haar.D6D9c.SL17Z13

/-- `SL(2, 17) × Z_13`. -/
abbrev Grp := SL17.Grp × Multiplicative (ZMod 13)

/-- The element with index `n`, for `n < 63648`. -/
def grpOf (n : ℕ) : Grp :=
  (SL17.grpOf (n / 13), Multiplicative.ofAdd ((n % 13 : ℕ) : ZMod 13))

/-- The index of `g = (M, z)`. -/
def enc (g : Grp) : ℕ :=
  13 * SL17.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val

theorem enc_lt (g : Grp) : enc g < 63648 := by
  have h1 := SL17.enc_lt g.1
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  unfold enc
  omega

theorem grpOf_enc (g : Grp) : grpOf (enc g) = g := by
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  have hdiv : (13 * SL17.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val) / 13
      = SL17.enc g.1.a g.1.b g.1.c g.1.d := by omega
  have hmod : (13 * SL17.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val) % 13
      = (Multiplicative.toAdd g.2).val := by omega
  unfold grpOf enc
  rw [hdiv, hmod, ZMod.natCast_val, ZMod.cast_id', id, SL17.grpOf_enc]
  simp

theorem enc_grpOf {n : ℕ} (hn : n < 63648) : enc (grpOf n) = n := by
  have hz : (((n % 13 : ℕ) : ZMod 13)).val = n % 13 := by
    rw [ZMod.val_natCast]
    exact Nat.mod_mod_of_dvd n (by norm_num)
  have hsl : SL17.enc (SL17.grpOf (n / 13)).a (SL17.grpOf (n / 13)).b (SL17.grpOf (n / 13)).c
      (SL17.grpOf (n / 13)).d = n / 13 := by
    obtain ⟨ha, hb, hc, hd⟩ := SL17.grpOf_fields (n := n / 13) (by omega)
    rw [ha, hb, hc, hd]
    exact SL17.enc_quad (n / 13) (by omega)
  have hval : (Multiplicative.toAdd (Multiplicative.ofAdd ((n % 13 : ℕ) : ZMod 13))).val = n % 13 := hz
  unfold enc grpOf
  simp only [hsl, hval]
  omega

/-- The numbering of `SL(2, 17) × Z_13`: `Grp ≃ Fin 63648`. -/
def equiv63648 : Grp ≃ Fin 63648 where
  toFun g := ⟨enc g, enc_lt g⟩
  invFun n := grpOf n.1
  left_inv g := grpOf_enc g
  right_inv n := by
    apply Fin.ext
    exact enc_grpOf n.2

end BipartiteDD.Haar.D6D9c.SL17Z13
