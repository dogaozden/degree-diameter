import BipartiteDD.LeanMaxx.Omega45b.Defs
import BipartiteDD.Hexagon.Main

/-!
# Points of `Q(6,7)` versus vectors, and collinear triples

* `card_pts_mul`: for a predicate `P` on vectors invariant under nonzero scalars,
  `6 · #{singular points x | P x} = #{singular nonzero vectors v | P v}`.
* `perp_of_dependent`: three pairwise distinct singular points whose representatives are linearly dependent
  (they lie on one projective line) are pairwise perpendicular (the line is totally singular).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace BipartiteDD.LeanMaxx.Omega45b

open BipartiteDD.Hexagon Finset

/-- Points versus vectors. -/
theorem card_pts_mul (P : V7 F7 → Prop) [DecidablePred P]
    (hP : ∀ (c : F7) (v : V7 F7), c ≠ 0 → (P (c • v) ↔ P v)) :
    6 * (Finset.univ.filter fun x : SPt F7 => P x.1.rep).card =
      (Finset.univ.filter fun v : V7 F7 => v ≠ 0 ∧ Qf v = 0 ∧ P v).card := by
  classical
  -- vectors: the subtype `{v // v ≠ 0 ∧ Qf v = 0 ∧ P v}`
  have h1 : (Finset.univ.filter fun v : V7 F7 => v ≠ 0 ∧ Qf v = 0 ∧ P v).card =
      Fintype.card {pc : SPt F7 × F7ˣ // P ((pc.2 : F7) • pc.1.1.rep)} := by
    rw [← Fintype.card_subtype]
    refine Fintype.card_congr (Equiv.symm ?_)
    refine ((sptProdUnitsEquiv (F := F7)).subtypeEquiv (p := fun pc => P ((pc.2 : F7) • pc.1.1.rep))
      (q := fun v => P v.1) (fun pc => Iff.rfl)).trans ?_
    exact
      { toFun := fun v => ⟨v.1.1, v.1.2.1, v.1.2.2, v.2⟩
        invFun := fun v => ⟨⟨v.1, v.2.1, v.2.2.1⟩, v.2.2.2⟩
        left_inv := fun v => rfl
        right_inv := fun v => rfl }
  have h2 : Fintype.card {pc : SPt F7 × F7ˣ // P ((pc.2 : F7) • pc.1.1.rep)} =
      Fintype.card {x : SPt F7 // P x.1.rep} * Fintype.card F7ˣ := by
    rw [← Fintype.card_prod]
    refine Fintype.card_congr ?_
    exact
      { toFun := fun pc => (⟨pc.1.1, (hP _ _ pc.1.2.ne_zero).1 pc.2⟩, pc.1.2)
        invFun := fun xc => ⟨(xc.1.1, xc.2), (hP _ _ xc.2.ne_zero).2 xc.1.2⟩
        left_inv := fun pc => rfl
        right_inv := fun xc => rfl }
  have h3 : Fintype.card F7ˣ = 6 := by
    rw [ZMod.card_units_eq_totient]; decide
  rw [h1, h2, h3, Fintype.card_subtype, mul_comm]

/-- If `a x + b y + c z = 0` with `a, b, c ≠ 0` and `x, y, z` singular, then `x ⟂ y`. -/
theorem bf_eq_zero_of_relation {x y z : V7 F7} (hx : Qf x = 0) (hy : Qf y = 0) (hz : Qf z = 0)
    {a b c : F7} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (h : a • x + b • y + c • z = 0) :
    Bf x y = 0 := by
  have h1 : a • x + b • y = -(c • z) := by
    rw [eq_neg_iff_add_eq_zero]; exact h
  have h2 : Qf (a • x + b • y) = 0 := by
    rw [h1]
    have := Qf_smul (-c) z
    rw [neg_smul, hz, mul_zero] at this
    exact this
  rw [Qf_add, Qf_smul, Qf_smul, hx, hy] at h2
  have h3 : Bf (a • x) (b • y) = a * b * Bf x y := by
    simp only [Bf, Pi.smul_apply, smul_eq_mul]; ring
  rw [h3] at h2
  simp only [mul_zero, zero_add] at h2
  rcases mul_eq_zero.1 h2 with h4 | h4
  · exact absurd h4 (mul_ne_zero ha hb)
  · exact h4

/-- Two distinct singular points have independent representatives. -/
theorem lin_indep_pair {x y : SPt F7} (hxy : x ≠ y) {a b : F7}
    (h : a • x.1.rep + b • y.1.rep = 0) : a = 0 ∧ b = 0 := by
  have hi : LinearIndependent F7 ![x.1.rep, y.1.rep] := by
    have := (Projectivization.independent_pair_iff_ne x.1 y.1).2 (fun h => hxy (Subtype.ext h))
    have h' := (Projectivization.independent_iff.1 this)
    convert h' using 1
    ext i; fin_cases i <;> rfl
  have := (LinearIndependent.pair_iff.1 hi) a b h
  exact this

/-- **Collinear triples are perpendicular.** If three pairwise distinct singular points `x, y, z` have linearly
dependent representatives, then `x ⟂ y`, `x ⟂ z` and `y ⟂ z`. -/
theorem perp_of_dependent {x y z : SPt F7} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdep : ¬ LinearIndependent F7 ![x.1.rep, y.1.rep, z.1.rep]) :
    Bf x.1.rep y.1.rep = 0 ∧ Bf x.1.rep z.1.rep = 0 ∧ Bf y.1.rep z.1.rep = 0 := by
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hg, i, hi⟩ := hdep
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hg
  have hg' : g 0 • x.1.rep + g 1 • y.1.rep + g 2 • z.1.rep = 0 := by simpa using hg
  have hx := x.2
  have hy := y.2
  have hz := z.2
  -- all three coefficients are nonzero
  have n2 : g 2 ≠ 0 := by
    intro h2
    rw [h2, zero_smul, add_zero] at hg'
    obtain ⟨h0, h1⟩ := lin_indep_pair hxy hg'
    fin_cases i <;> simp_all
  have n1 : g 1 ≠ 0 := by
    intro h1
    rw [h1, zero_smul, add_zero] at hg'
    obtain ⟨h0, h2⟩ := lin_indep_pair hxz hg'
    fin_cases i <;> simp_all
  have n0 : g 0 ≠ 0 := by
    intro h0
    rw [h0, zero_smul, zero_add] at hg'
    obtain ⟨h1, h2⟩ := lin_indep_pair hyz hg'
    fin_cases i <;> simp_all
  refine ⟨bf_eq_zero_of_relation hx hy hz n0 n1 n2 hg', ?_, ?_⟩
  · refine bf_eq_zero_of_relation hx hz hy n0 n2 n1 ?_
    rw [← hg']; abel
  · refine bf_eq_zero_of_relation hy hz hx n1 n2 n0 ?_
    rw [← hg']; abel

end BipartiteDD.LeanMaxx.Omega45b
