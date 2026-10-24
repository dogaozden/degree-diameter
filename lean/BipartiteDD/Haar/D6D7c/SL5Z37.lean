import BipartiteDD.Haar.D6D7c.SL5

/-! The group `SL(2, 5) × Z_37` of order 4440, with a computable numbering by `Fin 4440`.

The `Z_37` factor is `Multiplicative (ZMod 37)`. The element with index `n` is `(grpOf (n / 37), n % 37)`,
and the index of `(g, z)` is `37 * enc g + z`, where `enc g` is the index of `g` in `SL5`. -/

namespace BipartiteDD.Haar.D6D7c.SL5Z37

/-- `SL(2, 5) × Z_37`. -/
abbrev Grp := SL5.Grp × Multiplicative (ZMod 37)

/-- The element with index `n`, for `n < 4440`. -/
def grpOf (n : ℕ) : Grp :=
  (SL5.grpOf (n / 37), Multiplicative.ofAdd ((n % 37 : ℕ) : ZMod 37))

/-- The index of `g = (M, z)`. -/
def enc (g : Grp) : ℕ :=
  37 * SL5.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val

theorem enc_lt (g : Grp) : enc g < 4440 := by
  have h1 := SL5.enc_lt g.1
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  unfold enc
  omega

theorem grpOf_enc (g : Grp) : grpOf (enc g) = g := by
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  have hdiv : (37 * SL5.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val) / 37
      = SL5.enc g.1.a g.1.b g.1.c g.1.d := by omega
  have hmod : (37 * SL5.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val) % 37
      = (Multiplicative.toAdd g.2).val := by omega
  unfold grpOf enc
  rw [hdiv, hmod, ZMod.natCast_val, ZMod.cast_id', id, SL5.grpOf_enc]
  simp

theorem enc_grpOf {n : ℕ} (hn : n < 4440) : enc (grpOf n) = n := by
  have hz : (((n % 37 : ℕ) : ZMod 37)).val = n % 37 := by
    rw [ZMod.val_natCast]
    exact Nat.mod_mod_of_dvd n (by norm_num)
  have hsl : SL5.enc (SL5.grpOf (n / 37)).a (SL5.grpOf (n / 37)).b (SL5.grpOf (n / 37)).c
      (SL5.grpOf (n / 37)).d = n / 37 := by
    obtain ⟨ha, hb, hc, hd⟩ := SL5.grpOf_fields (n := n / 37) (by omega)
    rw [ha, hb, hc, hd]
    exact SL5.enc_quad (n / 37) (by omega)
  have hval : (Multiplicative.toAdd (Multiplicative.ofAdd ((n % 37 : ℕ) : ZMod 37))).val = n % 37 := hz
  unfold enc grpOf
  simp only [hsl, hval]
  omega

/-- The numbering of `SL(2, 5) × Z_37`: `Grp ≃ Fin 4440`. -/
def equiv4440 : Grp ≃ Fin 4440 where
  toFun g := ⟨enc g, enc_lt g⟩
  invFun n := grpOf n.1
  left_inv g := grpOf_enc g
  right_inv n := by
    apply Fin.ext
    exact enc_grpOf n.2

end BipartiteDD.Haar.D6D7c.SL5Z37
