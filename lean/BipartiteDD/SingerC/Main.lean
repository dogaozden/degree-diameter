import BipartiteDD.SingerC.Count

/-! Proposition C, stated for an arbitrary 2-dimensional totally isotropic F-subspace `U`:
the nonzero vectors of `U` lying in classes `a` or `q - a` number `2 (q - 1)`, i.e. the points of
`U` in those classes number exactly 2. -/

namespace BipartiteDD.SingerC

open Finset

namespace Setting

variable {K : Type*} [Field K] [Fintype K] {p : ℕ} [Fact p.Prime] [CharP K p]
variable (S : Setting K p)

theorem propC_pair {a : ℕ} (ha : a ≤ S.q) {x y : K}
    (hind : ∀ s t : K, s ∈ S.F → t ∈ S.F → s * x + t * y = 0 → s = 0 ∧ t = 0)
    (ht : S.B x y = 0) :
    Nat.card {st : S.F × S.F // st ≠ 0 ∧
        (S.InClass a ((st.1 : K) * x + (st.2 : K) * y)
          ∨ S.InClass (S.q - a) ((st.1 : K) * x + (st.2 : K) * y))} = 2 * (S.q - 1) := by
  have h := S.card_union_class ha hind ht
  have hq1 : 1 ≤ S.q := S.q_odd.pos
  have h2 : ((2 * (S.q - 1) : ℕ) : ℤ) = 2 * ((S.q : ℤ) - 1) := by
    push_cast [Nat.cast_sub hq1]
    ring
  rw [← h2] at h
  exact_mod_cast h

/-- Proposition C for a 2-dimensional totally isotropic `F`-subspace `U` of `K`: the nonzero
vectors of `U` in classes `a` or `q - a` are `2 (q - 1)` in number, i.e. the points of `U` in
these two classes are exactly 2. -/
theorem propC_subspace {a : ℕ} (ha : a ≤ S.q) (U : Submodule S.F K)
    (hU : Module.finrank S.F U = 2) (hTI : ∀ u ∈ U, ∀ v ∈ U, S.B u v = 0) :
    Nat.card {u : U // u ≠ 0 ∧ (S.InClass a (u : K) ∨ S.InClass (S.q - a) (u : K))}
      = 2 * (S.q - 1) := by
  classical
  let b : Module.Basis (Fin 2) S.F U := Module.finBasisOfFinrankEq S.F U hU
  let e : (S.F × S.F) ≃ U := (finTwoArrowEquiv S.F).symm.trans b.equivFun.symm.toEquiv
  have he : ∀ st : S.F × S.F, ((e st : U) : K) = (st.1 : K) * (b 0 : K) + (st.2 : K) * (b 1 : K) := by
    intro st
    simp [e, Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, finTwoArrowEquiv]
    rfl
  have e0 : e 0 = 0 := Subtype.ext (by rw [he]; simp)
  have hind : ∀ s t : K, s ∈ S.F → t ∈ S.F → s * (b 0 : K) + t * (b 1 : K) = 0 →
      s = 0 ∧ t = 0 := by
    intro s t hs ht hst
    have h0 : e (⟨s, hs⟩, ⟨t, ht⟩) = e 0 := by
      rw [e0]
      apply Subtype.ext
      rw [he]
      exact hst
    have h1 := Prod.mk_eq_zero.mp (e.injective h0)
    exact ⟨congrArg Subtype.val h1.1, congrArg Subtype.val h1.2⟩
  have ht : S.B (b 0 : K) (b 1 : K) = 0 := hTI _ (b 0).2 _ (b 1).2
  have hiff : ∀ st : S.F × S.F,
      (st ≠ 0 ∧ (S.InClass a ((st.1 : K) * (b 0 : K) + (st.2 : K) * (b 1 : K))
          ∨ S.InClass (S.q - a) ((st.1 : K) * (b 0 : K) + (st.2 : K) * (b 1 : K))))
        ↔ (e st ≠ 0 ∧ (S.InClass a ((e st : U) : K) ∨ S.InClass (S.q - a) ((e st : U) : K))) := by
    intro st
    rw [he]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (e.injective (h.trans e0.symm)), h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (by rw [h, e0]), h2⟩
  rw [← Nat.card_congr (Equiv.subtypeEquiv e (fun st => hiff st))]
  exact S.propC_pair ha hind ht

end Setting

end BipartiteDD.SingerC
