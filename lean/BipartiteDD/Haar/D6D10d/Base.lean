import BipartiteDD.Haar.D6D10d.SL5
import BipartiteDD.Haar.D6D10d.PSL7
import Mathlib.Logic.Equiv.Fin.Basic

/-! The group `G = SL(2, 5) × PSL(2, 7) × Z_13` of the Δ6·D10 record (order 262080), and its numbering by `Fin 262080`.

`G` is a structure with componentwise operations (not the `Prod` group), so that the projections of a product are
computed by the direct operations of `SL5.Grp`, `PSL7.Grp` and `Multiplicative (ZMod 13)`; this keeps the
defeq checks between the word and the Nat-level check cheap. The index of `x` is
`(SL5.enc x.s * 168 + PSL7.enc x.p) * 13 + x.z`. -/

namespace BipartiteDD.Haar.D6D10d

/-- The group `SL(2, 5) × PSL(2, 7) × Z_13`; the last factor is `Multiplicative (ZMod 13)`, so it adds. -/
@[ext]
structure G where
  s : SL5.Grp
  p : PSL7.Grp
  z : Multiplicative (ZMod 13)
  deriving DecidableEq

instance : Mul G := ⟨fun x y => ⟨x.s * y.s, x.p * y.p, x.z * y.z⟩⟩
instance : One G := ⟨⟨1, 1, 1⟩⟩
instance : Inv G := ⟨fun x => ⟨x.s⁻¹, x.p⁻¹, x.z⁻¹⟩⟩

theorem mul_s (x y : G) : (x * y).s = x.s * y.s := rfl
theorem mul_p (x y : G) : (x * y).p = x.p * y.p := rfl
theorem mul_z (x y : G) : (x * y).z = x.z * y.z := rfl
theorem one_s : (1 : G).s = 1 := rfl
theorem one_p : (1 : G).p = 1 := rfl
theorem one_z : (1 : G).z = 1 := rfl
theorem inv_s (x : G) : (x⁻¹).s = x.s⁻¹ := rfl
theorem inv_p (x : G) : (x⁻¹).p = x.p⁻¹ := rfl
theorem inv_z (x : G) : (x⁻¹).z = x.z⁻¹ := rfl

instance : Group G where
  mul_assoc x y z := by
    refine G.ext ?_ ?_ ?_ <;> simp only [mul_s, mul_p, mul_z, mul_assoc]
  one_mul x := by
    refine G.ext ?_ ?_ ?_ <;> simp only [mul_s, mul_p, mul_z, one_s, one_p, one_z, one_mul]
  mul_one x := by
    refine G.ext ?_ ?_ ?_ <;> simp only [mul_s, mul_p, mul_z, one_s, one_p, one_z, mul_one]
  inv_mul_cancel x := by
    refine G.ext ?_ ?_ ?_ <;>
      simp only [mul_s, mul_p, mul_z, inv_s, inv_p, inv_z, one_s, one_p, one_z, inv_mul_cancel]

/-- The index of `x`. -/
def idxG (x : G) : ℕ :=
  (SL5.enc x.s.a x.s.b x.s.c x.s.d * 168 + PSL7.enc x.p.a x.p.b x.p.c x.p.d) * 13
    + (Multiplicative.toAdd x.z).val

/-- The element with index `n`. -/
def gOf (n : ℕ) : G :=
  ⟨SL5.grpOf (n / 13 / 168), PSL7.grpP (n / 13 % 168), Multiplicative.ofAdd ((n % 13 : ℕ) : ZMod 13)⟩

theorem idxG_lt (x : G) : idxG x < 262080 := by
  have h1 := SL5.enc_lt x.s
  have h2 := PSL7.enc_lt x.p
  have h3 := ZMod.val_lt (Multiplicative.toAdd x.z)
  unfold idxG
  omega

theorem gOf_idxG (x : G) : gOf (idxG x) = x := by
  have h1 := SL5.enc_lt x.s
  have h2 := PSL7.enc_lt x.p
  have h3 := ZMod.val_lt (Multiplicative.toAdd x.z)
  have e1 : idxG x / 13 / 168 = SL5.enc x.s.a x.s.b x.s.c x.s.d := by
    unfold idxG
    omega
  have e2 : idxG x / 13 % 168 = PSL7.enc x.p.a x.p.b x.p.c x.p.d := by
    unfold idxG
    omega
  have e3 : idxG x % 13 = (Multiplicative.toAdd x.z).val := by
    unfold idxG
    omega
  unfold gOf
  rw [e1, e2, e3, SL5.grpOf_enc, PSL7.grpP_enc, ZMod.natCast_zmod_val]
  rfl

theorem idxG_gOf (n : ℕ) (hn : n < 262080) : idxG (gOf n) = n := by
  have hx : n / 13 / 168 < 120 := by omega
  have hy : n / 13 % 168 < 168 := Nat.mod_lt _ (by norm_num)
  have h1 : SL5.enc (SL5.grpOf (n / 13 / 168)).a (SL5.grpOf (n / 13 / 168)).b
      (SL5.grpOf (n / 13 / 168)).c (SL5.grpOf (n / 13 / 168)).d = n / 13 / 168 := by
    obtain ⟨ha, hb, hc, hd⟩ := SL5.grpOf_fields hx
    rw [ha, hb, hc, hd]
    exact SL5.enc_quad _ hx
  have h2 : PSL7.enc (PSL7.grpP (n / 13 % 168)).a (PSL7.grpP (n / 13 % 168)).b
      (PSL7.grpP (n / 13 % 168)).c (PSL7.grpP (n / 13 % 168)).d = n / 13 % 168 :=
    PSL7.enc_grpP _ hy
  have h3 : (Multiplicative.toAdd (Multiplicative.ofAdd ((n % 13 : ℕ) : ZMod 13))).val = n % 13 := by
    show (((n % 13 : ℕ) : ZMod 13)).val = n % 13
    rw [ZMod.val_natCast, Nat.mod_mod]
  unfold idxG gOf
  dsimp only
  rw [h1, h2, h3]
  omega

/-- The numbering of `G` by `Fin 262080`. -/
def equivG : G ≃ Fin 262080 where
  toFun x := ⟨idxG x, idxG_lt x⟩
  invFun n := gOf n.1
  left_inv x := gOf_idxG x
  right_inv n := Fin.ext (idxG_gOf n.1 n.2)

/-- `G ⊕ G ≃ Fin 524160`: the two sides of the Haar graph. -/
def haarVert : G ⊕ G ≃ Fin 524160 :=
  (Equiv.sumCongr equivG equivG).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D6D10d
