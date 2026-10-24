import BipartiteDD.Haar.D5D7b.PGL5

/-! The group `PGL(2, 5) × Z_13` of order 1560, with a computable numbering by `Fin 1560`.

The `Z_13` factor is `Multiplicative (ZMod 13)`. The element with index `n` is `(grpOf (n / 13), n % 13)`, and the index
of `(g, z)` is `13 * enc g + z`, where `enc g` is the index of `g` in `PGL5`. -/

namespace BipartiteDD.Haar.D5D7b.PGL5Z13

/-- `PGL(2, 5) × Z_13`. -/
abbrev Grp := PGL5.Grp × Multiplicative (ZMod 13)

/-- The element with index `n`. -/
def grpOf (n : ℕ) : Grp :=
  (PGL5.grpOf (n / 13), Multiplicative.ofAdd ((n % 13 : ℕ) : ZMod 13))

/-- The index of `g = (M, z)`. -/
def enc (g : Grp) : ℕ :=
  13 * PGL5.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val

theorem enc_lt (g : Grp) : enc g < 1560 := by
  have h1 := PGL5.enc_lt g.1
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  unfold enc
  omega

theorem grpOf_enc (g : Grp) : grpOf (enc g) = g := by
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  have hdiv : (13 * PGL5.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val) / 13
      = PGL5.enc g.1.a g.1.b g.1.c g.1.d := by omega
  have hmod : (13 * PGL5.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val) % 13
      = (Multiplicative.toAdd g.2).val := by omega
  unfold grpOf enc
  rw [hdiv, hmod, ZMod.natCast_val, ZMod.cast_id', id, PGL5.grpOf_enc]
  simp

theorem enc_grpOf {n : ℕ} (hn : n < 1560) : enc (grpOf n) = n := by
  have hp : PGL5.enc (PGL5.grpOf (n / 13)).a (PGL5.grpOf (n / 13)).b (PGL5.grpOf (n / 13)).c
      (PGL5.grpOf (n / 13)).d = n / 13 := PGL5.enc_grpOf (by omega)
  have hz : (Multiplicative.toAdd (Multiplicative.ofAdd ((n % 13 : ℕ) : ZMod 13))).val = n % 13 := by
    show (((n % 13 : ℕ) : ZMod 13)).val = n % 13
    rw [ZMod.val_natCast, Nat.mod_mod]
  show 13 * PGL5.enc (PGL5.grpOf (n / 13)).a (PGL5.grpOf (n / 13)).b (PGL5.grpOf (n / 13)).c
      (PGL5.grpOf (n / 13)).d + (Multiplicative.toAdd (Multiplicative.ofAdd ((n % 13 : ℕ) : ZMod 13))).val = n
  rw [hp, hz]
  omega

/-- The numbering of `PGL(2, 5) × Z_13`: `Grp ≃ Fin 1560`. -/
def equiv1560 : Grp ≃ Fin 1560 where
  toFun g := ⟨enc g, enc_lt g⟩
  invFun n := grpOf n.1
  left_inv g := grpOf_enc g
  right_inv n := by
    apply Fin.ext
    exact enc_grpOf n.2

end BipartiteDD.Haar.D5D7b.PGL5Z13
