import BipartiteDD.Haar.PGL37

/-! The group `PGL(2, 37) × Z_5` of order 253080, with a computable numbering by `Fin 253080`.

The `Z_5` factor is `Multiplicative (ZMod 5)`. The element with index `n` is `(grpOf (n / 5), n % 5)`, and the index
of `(g, z)` is `5 * enc g + z`, where `enc g` is the index of `g` in `PGL37`. -/

namespace BipartiteDD.Haar.PGL37Z5

/-- `PGL(2, 37) × Z_5`. -/
abbrev Grp := PGL37.Grp × Multiplicative (ZMod 5)

/-- The element with index `n`. -/
def grpOf (n : ℕ) : Grp :=
  (PGL37.grpOf (n / 5), Multiplicative.ofAdd ((n % 5 : ℕ) : ZMod 5))

/-- The index of `g = (M, z)`. -/
def enc (g : Grp) : ℕ :=
  5 * PGL37.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val

theorem enc_lt (g : Grp) : enc g < 253080 := by
  have h1 := PGL37.enc_lt g.1
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  unfold enc
  omega

theorem grpOf_enc (g : Grp) : grpOf (enc g) = g := by
  have h2 := ZMod.val_lt (Multiplicative.toAdd g.2)
  have hdiv : (5 * PGL37.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val) / 5
      = PGL37.enc g.1.a g.1.b g.1.c g.1.d := by omega
  have hmod : (5 * PGL37.enc g.1.a g.1.b g.1.c g.1.d + (Multiplicative.toAdd g.2).val) % 5
      = (Multiplicative.toAdd g.2).val := by omega
  unfold grpOf enc
  rw [hdiv, hmod, ZMod.natCast_val, ZMod.cast_id', id, PGL37.grpOf_enc]
  simp

theorem enc_grpOf {n : ℕ} (hn : n < 253080) : enc (grpOf n) = n := by
  have hp : PGL37.enc (PGL37.grpOf (n / 5)).a (PGL37.grpOf (n / 5)).b (PGL37.grpOf (n / 5)).c
      (PGL37.grpOf (n / 5)).d = n / 5 := PGL37.enc_grpOf (by omega)
  have hz : (Multiplicative.toAdd (Multiplicative.ofAdd ((n % 5 : ℕ) : ZMod 5))).val = n % 5 := by
    show (((n % 5 : ℕ) : ZMod 5)).val = n % 5
    rw [ZMod.val_natCast, Nat.mod_mod]
  show 5 * PGL37.enc (PGL37.grpOf (n / 5)).a (PGL37.grpOf (n / 5)).b (PGL37.grpOf (n / 5)).c
      (PGL37.grpOf (n / 5)).d + (Multiplicative.toAdd (Multiplicative.ofAdd ((n % 5 : ℕ) : ZMod 5))).val = n
  rw [hp, hz]
  omega

/-- The numbering of `PGL(2, 37) × Z_5`: `Grp ≃ Fin 253080`. -/
def equiv253080 : Grp ≃ Fin 253080 where
  toFun g := ⟨enc g, enc_lt g⟩
  invFun n := grpOf n.1
  left_inv g := grpOf_enc g
  right_inv n := by
    apply Fin.ext
    exact enc_grpOf n.2

end BipartiteDD.Haar.PGL37Z5
