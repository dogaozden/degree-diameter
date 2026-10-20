import BipartiteDD.SingerC.Main
import BipartiteDD.GQST.Defs

/-! Corollary C1, step 2: the generalized quadrangle W(3,q) on the Singer setting (work in progress).

Points are the projective points `ℙ F K` (1-dimensional `F`-subspaces of `K`); lines are the
2-dimensional totally isotropic `F`-subspaces for the form `S.B`; `p ∈ l` means `p ≤ l`.
This file is not on the import chain of `BipartiteDD` until it is sorry-free. -/

namespace BipartiteDD.SingerC

open Module Projectivization
open scoped LinearAlgebra.Projectivization

namespace Setting

variable {K : Type*} [Field K] [Fintype K] {p : ℕ} [Fact p.Prime] [CharP K p]
variable (S : Setting K p)

instance : FiniteDimensional S.F K := Module.Finite.of_finite

theorem tr4_mem_F (z : K) : S.tr4 z ∈ S.F := by
  rw [mem_F]
  unfold tr4
  simp only [add_pow_q1]
  have h1 : (z ^ S.q) ^ S.q = z ^ S.q ^ 2 := by rw [← pow_mul, sq]
  have h2 : (z ^ S.q ^ 2) ^ S.q = z ^ S.q ^ 3 := by rw [← pow_mul, ← pow_succ]
  have h3 : (z ^ S.q ^ 3) ^ S.q = z := by
    rw [← pow_mul, ← pow_succ, show (3 : ℕ) + 1 = 4 from rfl, S.pow_card]
  rw [h1, h2, h3]
  ring

theorem B_mem_F (x y : K) : S.B x y ∈ S.F := S.tr4_mem_F _

/-- `B v · : K → F` as a linear map over `F`. -/
def Bfun (v : K) : K →ₗ[S.F] S.F where
  toFun x := ⟨S.B v x, S.B_mem_F v x⟩
  map_add' x y := Subtype.ext (S.B_add_right v x y)
  map_smul' c x := Subtype.ext (S.B_smul_right c c.2 v x)

theorem finrank_K : finrank S.F K = 4 := by
  have h := Module.card_eq_pow_finrank (K := S.F) (V := K)
  have hK : Fintype.card K = S.q ^ 4 := S.card_eq'
  have hF : Fintype.card S.F = S.q := by rw [← Nat.card_eq_fintype_card]; exact S.natCard_F
  rw [hK, hF] at h
  exact (Nat.pow_right_injective (S.one_lt_q : 2 ≤ S.q) h).symm

/-- Points of `W(3,q)`: the projective points of `K` over `F`. -/
theorem card_points_le (U : Submodule S.F K) :
    Nat.card {x : ℙ S.F K // x.submodule ≤ U} = Nat.card (ℙ S.F U) := by
  let f : ℙ S.F U → ℙ S.F K := Projectivization.map U.subtype (fun a b h => Subtype.ext h)
  have hf : Function.Injective f := Projectivization.map_injective _ (fun a b h => Subtype.ext h)
  have hmem : ∀ q : ℙ S.F U, (f q).submodule ≤ U := by
    intro q
    induction q using Projectivization.ind with
    | h v hv =>
      have e : f (Projectivization.mk S.F v hv) = Projectivization.mk S.F (v : K)
          (fun h => hv (Subtype.ext h)) := Projectivization.map_mk _ _ _ _
      rw [e, Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem]
      exact v.2
  refine (Nat.card_congr (Equiv.ofBijective (fun q => ⟨f q, hmem q⟩) ⟨?_, ?_⟩)).symm
  · intro a b hab
    exact hf (congrArg Subtype.val hab)
  · rintro ⟨x, hx⟩
    induction x using Projectivization.ind with
    | h v hv =>
      have hvU : v ∈ U := by
        rw [Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem] at hx
        exact hx
      refine ⟨Projectivization.mk S.F (⟨v, hvU⟩ : U) (fun h => hv (congrArg Subtype.val h)), ?_⟩
      apply Subtype.ext
      exact Projectivization.map_mk U.subtype (fun a b h => Subtype.ext h) _ _

theorem card_points_on (U : Submodule S.F K) (hU : finrank S.F U = 2) :
    Nat.card {x : ℙ S.F K // x.submodule ≤ U} = S.q + 1 := by
  rw [S.card_points_le U, Projectivization.card_of_finrank_two S.F U hU, S.natCard_F]

/-- Lines of `W(3,q)`: the totally isotropic 2-dimensional `F`-subspaces of `K`. -/
def TILine : Type _ :=
  {U : Submodule S.F K // finrank S.F U = 2 ∧ ∀ u ∈ U, ∀ u' ∈ U, S.B u u' = 0}

instance : Membership (ℙ S.F K) S.TILine := ⟨fun l x => x.submodule ≤ l.1⟩

theorem pts_on_line (l : S.TILine) : Nat.card {x : ℙ S.F K // x ∈ l} = S.q + 1 :=
  S.card_points_on l.1 l.2.1

theorem finrank_sup_of_ne {x y : ℙ S.F K} (hxy : x ≠ y) :
    finrank S.F ↥(x.submodule ⊔ y.submodule) = 2 := by
  have h1 : finrank S.F x.submodule = 1 := x.finrank_submodule
  have h2 : finrank S.F y.submodule = 1 := y.finrank_submodule
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq x.submodule y.submodule
  have hinf : finrank S.F ↥(x.submodule ⊓ y.submodule) = 0 := by
    by_contra hne
    have hle : x.submodule ⊓ y.submodule ≤ x.submodule := inf_le_left
    have hle' : x.submodule ⊓ y.submodule ≤ y.submodule := inf_le_right
    have e1 : x.submodule ⊓ y.submodule = x.submodule :=
      Submodule.eq_of_le_of_finrank_le hle (by omega)
    have e2 : x.submodule ⊓ y.submodule = y.submodule :=
      Submodule.eq_of_le_of_finrank_le hle' (by omega)
    exact hxy (Projectivization.submodule_injective (e1.symm.trans e2))
  omega

theorem B_point (x : ℙ S.F K) {a a' : K} (ha : a ∈ x.submodule) (ha' : a' ∈ x.submodule) :
    S.B a a' = 0 := by
  rw [Projectivization.submodule_eq] at ha ha'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
  obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp ha'
  show S.B ((c : K) * x.rep) ((c' : K) * x.rep) = 0
  rw [S.B_smul_left _ c.2, S.B_smul_right _ c'.2, S.B_self, mul_zero, mul_zero]

theorem B_cross (x : ℙ S.F K) {a b : K} (ha : a ∈ x.submodule) (hb : S.B x.rep b = 0) :
    S.B a b = 0 := by
  rw [Projectivization.submodule_eq] at ha
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
  show S.B ((c : K) * x.rep) b = 0
  rw [S.B_smul_left _ c.2, hb, mul_zero]

theorem B_sup {U V : Submodule S.F K} (hUU : ∀ a ∈ U, ∀ a' ∈ U, S.B a a' = 0)
    (hVV : ∀ b ∈ V, ∀ b' ∈ V, S.B b b' = 0) (hUV : ∀ a ∈ U, ∀ b ∈ V, S.B a b = 0) :
    ∀ u ∈ U ⊔ V, ∀ u' ∈ U ⊔ V, S.B u u' = 0 := by
  have hVU : ∀ a ∈ U, ∀ b ∈ V, S.B b a = 0 := fun a ha b hb => by
    rw [S.B_antisymm, hUV a ha b hb, neg_zero]
  intro u hu u' hu'
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
  obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.mp hu'
  simp [S.B_add_left, S.B_add_right, hUU a ha a' ha', hUV a ha b' hb', hVU a' ha' b hb,
    hVV b hb b' hb']

theorem Bfun_apply (v x : K) : S.Bfun v x = 0 ↔ S.B v x = 0 :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end Setting

end BipartiteDD.SingerC
