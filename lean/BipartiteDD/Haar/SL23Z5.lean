import BipartiteDD.Haar.SL23

/-! The group `SL(2, 23) × Z_5` of order 60720, with a computable numbering by `Fin 60720`.

The `Z_5` factor is `Multiplicative (ZMod 5)`. The element with index `n` is `(grpOf (n / 5), n % 5)`,
and the index of `(g, z)` is `5 * enc g + z`, where `enc g` is the index of `g` in `SL23`. -/

namespace BipartiteDD.Haar.SL23Z5

/-- `SL(2, 23) × Z_5`. -/
abbrev Grp := SL23.Grp × Multiplicative (ZMod 5)

/-- The element with index `n`, for `n < 60720`. -/
def grpOf (n : ℕ) : Grp :=
  (SL23.grpOf (n / 5), Multiplicative.ofAdd ((n % 5 : ℕ) : ZMod 5))

/-- The index of `g = (M, z)`. -/
def enc (g : Grp) : ℕ :=
  5 * SL23.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val

theorem enc_lt (g : Grp) : enc g < 60720 := by
  have h1 := SL23.enc_lt g.1
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  unfold enc
  omega

theorem grpOf_enc (g : Grp) : grpOf (enc g) = g := by
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  have hdiv : (5 * SL23.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val) / 5
      = SL23.enc g.1.a g.1.b g.1.c g.1.d := by omega
  have hmod : (5 * SL23.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val) % 5
      = (Multiplicative.toAdd g.2).val := by omega
  unfold grpOf enc
  rw [hdiv, hmod, ZMod.natCast_val, ZMod.cast_id', id, SL23.grpOf_enc]
  simp

theorem enc_grpOf {n : ℕ} (hn : n < 60720) : enc (grpOf n) = n := by
  have hz : (((n % 5 : ℕ) : ZMod 5)).val = n % 5 := by
    rw [ZMod.val_natCast]
    exact Nat.mod_mod_of_dvd n (by norm_num)
  have hsl : SL23.enc (SL23.grpOf (n / 5)).a (SL23.grpOf (n / 5)).b (SL23.grpOf (n / 5)).c
      (SL23.grpOf (n / 5)).d = n / 5 := by
    obtain ⟨ha, hb, hc, hd⟩ := SL23.grpOf_fields (n := n / 5) (by omega)
    rw [ha, hb, hc, hd]
    exact SL23.enc_quad (n / 5) (by omega)
  have hval : (Multiplicative.toAdd (Multiplicative.ofAdd ((n % 5 : ℕ) : ZMod 5))).val = n % 5 := hz
  unfold enc grpOf
  simp only [hsl, hval]
  omega

/-- The numbering of `SL(2, 23) × Z_5`: `Grp ≃ Fin 60720`. -/
def equiv60720 : Grp ≃ Fin 60720 where
  toFun g := ⟨enc g, enc_lt g⟩
  invFun n := grpOf n.1
  left_inv g := grpOf_enc g
  right_inv n := by
    apply Fin.ext
    exact enc_grpOf n.2

end BipartiteDD.Haar.SL23Z5
