import BipartiteDD.HexagonD7.Opposite

/-! Diameter 7 from a generalized hexagon, part 8: **Lemma 2**, a local duality for pairwise opposite sets.

If the closed 2-balls of the points of `R` are pairwise disjoint, those of the lines of `S` too, `τ : R ≃ S`, and
`|P| = |L|`, then some `σ : P ≃ L` has `σ r = τ r` and maps `ballP r` onto `ballL (τ r)`; hence `σ` satisfies
condition (R2) at every `r ∈ R`. Construction: a bijection `ballP r ≃ ballL (τ r)` fixing the centres for each
`r`, glued over the disjoint balls, and any bijection between the complements. -/

namespace BipartiteDD.HexagonD7

open Finset
open scoped Classical

variable {P L : Type*} [Fintype P] [Fintype L] {inc : P → L → Prop} {q : ℕ}
  (hdig : ∀ {p r : P} {M₁ M₂ : L}, p ≠ r → inc p M₁ → inc r M₁ → inc p M₂ → inc r M₂ → M₁ = M₂)
  (hP : ∀ p, (univ.filter (inc p)).card = q + 1) (hL : ∀ l, (univ.filter (fun p => inc p l)).card = q + 1)
  {R : Finset P} {S : Finset L}
  (hR : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → Disjoint (ballP inc r) (ballP inc s))
  (hS : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Disjoint (ballL inc a) (ballL inc b))
  (τ : R ≃ S)

section Construction

include hdig hP hL

/-- A bijection of the 2-balls of `r` and `τ r` sending the centre to the centre. -/
noncomputable def ballEquiv (r : R) : {z // z ∈ ballP inc r.1} ≃ {m // m ∈ ballL inc (τ r).1} :=
  let e0 : {z // z ∈ ballP inc r.1} ≃ {m // m ∈ ballL inc (τ r).1} :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_coe, Fintype.card_coe, card_ballP hdig hP hL, card_ballL hdig hP hL])
  e0.trans (Equiv.swap (e0 ⟨r.1, self_mem_ballP _⟩) ⟨(τ r).1, self_mem_ballL _⟩)

theorem ballEquiv_center (r : R) :
    ballEquiv hdig hP hL τ r ⟨r.1, self_mem_ballP _⟩ = ⟨(τ r).1, self_mem_ballL _⟩ := by
  simp [ballEquiv]

/-- The pointwise map on a ball (any value outside). -/
noncomputable def E (r : R) (z : P) : L :=
  if hz : z ∈ ballP inc r.1 then (ballEquiv hdig hP hL τ r ⟨z, hz⟩).1 else (τ r).1

theorem E_mem (r : R) {z : P} (hz : z ∈ ballP inc r.1) : E hdig hP hL τ r z ∈ ballL inc (τ r).1 := by
  rw [E, dif_pos hz]; exact (ballEquiv hdig hP hL τ r ⟨z, hz⟩).2

theorem E_inj (r : R) {z z' : P} (hz : z ∈ ballP inc r.1) (hz' : z' ∈ ballP inc r.1)
    (h : E hdig hP hL τ r z = E hdig hP hL τ r z') : z = z' := by
  rw [E, E, dif_pos hz, dif_pos hz'] at h
  have := (ballEquiv hdig hP hL τ r).injective (Subtype.ext h)
  exact congrArg Subtype.val this

theorem E_center (r : R) : E hdig hP hL τ r r.1 = (τ r).1 := by
  rw [E, dif_pos (self_mem_ballP _), ballEquiv_center]

end Construction

/-- The union of the balls of `R`. -/
noncomputable def bigA (inc : P → L → Prop) (R : Finset P) : Finset P := R.biUnion (ballP inc)

/-- The union of the balls of `S`. -/
noncomputable def bigB (inc : P → L → Prop) (S : Finset L) : Finset L := S.biUnion (ballL inc)

/-- The owner of a point of `bigA`. -/
noncomputable def own {z : P} (h : z ∈ bigA inc R) : R :=
  ⟨Classical.choose (mem_biUnion.1 h), (Classical.choose_spec (mem_biUnion.1 h)).1⟩

theorem own_spec {z : P} (h : z ∈ bigA inc R) : z ∈ ballP inc (own h).1 :=
  (Classical.choose_spec (mem_biUnion.1 h)).2

include hR in
theorem own_eq {z : P} (h : z ∈ bigA inc R) {r : P} (hr : r ∈ R) (hz : z ∈ ballP inc r) : (own h).1 = r := by
  by_contra hne
  exact Finset.disjoint_left.1 (hR _ (own h).2 r hr hne) (own_spec h) hz

include hS in
theorem tau_eq_of_mem {a b : S} {m : L} (ha : m ∈ ballL inc a.1) (hb : m ∈ ballL inc b.1) : a = b := by
  by_contra hne
  exact Finset.disjoint_left.1 (hS _ a.2 _ b.2 (fun h => hne (Subtype.ext h))) ha hb

section Glue

set_option linter.unusedSectionVars false
include hdig hP hL hR hS

/-- The glued map on `bigA`. -/
noncomputable def fA (z : {z // z ∈ bigA inc R}) : {m // m ∈ bigB inc S} :=
  ⟨E hdig hP hL τ (own z.2) z.1, mem_biUnion.2 ⟨(τ (own z.2)).1, (τ (own z.2)).2, E_mem hdig hP hL τ _ (own_spec z.2)⟩⟩

theorem fA_injective : Function.Injective (fA hdig hP hL τ) := by
  intro z z' h
  have hv : E hdig hP hL τ (own z.2) z.1 = E hdig hP hL τ (own z'.2) z'.1 := congrArg Subtype.val h
  have h1 := E_mem hdig hP hL τ (own z.2) (own_spec z.2)
  have h2 := E_mem hdig hP hL τ (own z'.2) (own_spec z'.2)
  rw [hv] at h1
  have hτ : τ (own z.2) = τ (own z'.2) := tau_eq_of_mem hS h1 h2
  have ho : own z.2 = own z'.2 := τ.injective hτ
  rw [ho] at hv
  have hz : z.1 ∈ ballP inc (own z'.2).1 := ho ▸ own_spec z.2
  exact Subtype.ext (E_inj hdig hP hL τ _ hz (own_spec z'.2) hv)

theorem card_bigA : (bigA inc R).card = R.card * (1 + (q + 1) * q) := by
  rw [bigA, card_biUnion hR, sum_congr rfl (fun r _ => card_ballP hdig hP hL r), sum_const, smul_eq_mul]

theorem card_bigB : (bigB inc S).card = S.card * (1 + (q + 1) * q) := by
  rw [bigB, card_biUnion hS, sum_congr rfl (fun a _ => card_ballL hdig hP hL a), sum_const, smul_eq_mul]

theorem fA_bijective : Function.Bijective (fA hdig hP hL τ) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fA_injective hdig hP hL hR hS τ, ?_⟩
  rw [Fintype.card_coe, Fintype.card_coe, card_bigA hdig hP hL hR hS, card_bigB hdig hP hL hR hS]
  have : R.card = S.card := by
    have := Fintype.card_congr τ; rwa [Fintype.card_coe, Fintype.card_coe] at this
  rw [this]

/-- **Lemma 2.** -/
theorem exists_local_duality (hcard : Fintype.card P = Fintype.card L) :
    ∃ σ : P ≃ L, (∀ r : R, σ r.1 = (τ r).1) ∧
      ∀ r ∈ R, ∀ p, Coll inc r p ↔ Conc inc (σ r) (σ p) := by
  have hc : Fintype.card {z // z ∉ bigA inc R} = Fintype.card {m // m ∉ bigB inc S} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_coe,
      card_bigA hdig hP hL hR hS, card_bigB hdig hP hL hR hS, hcard]
    have : R.card = S.card := by
      have := Fintype.card_congr τ; rwa [Fintype.card_coe, Fintype.card_coe] at this
    rw [this]
  let g : {z // z ∉ bigA inc R} ≃ {m // m ∉ bigB inc S} := Fintype.equivOfCardEq hc
  let σ : P ≃ L := ((Equiv.sumCompl (fun z => z ∈ bigA inc R)).symm.trans
    (Equiv.sumCongr (Equiv.ofBijective _ (fA_bijective hdig hP hL hR hS τ)) g)).trans
    (Equiv.sumCompl (fun m => m ∈ bigB inc S))
  have hσA : ∀ z (hz : z ∈ bigA inc R), σ z = E hdig hP hL τ (own hz) z := by
    intro z hz
    simp only [σ, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hz, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.sumCompl_apply_inl, Equiv.ofBijective_apply, fA]
  have hσB : ∀ z, z ∉ bigA inc R → σ z ∉ bigB inc S := by
    intro z hz
    simp only [σ, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg hz, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.sumCompl_apply_inr]
    exact (g ⟨z, hz⟩).2
  have hrA : ∀ r ∈ R, r ∈ bigA inc R := fun r hr => mem_biUnion.2 ⟨r, hr, self_mem_ballP r⟩
  have hσr : ∀ r : R, σ r.1 = (τ r).1 := by
    intro r
    rw [hσA r.1 (hrA r.1 r.2)]
    have ho : own (hrA r.1 r.2) = r := Subtype.ext (own_eq hR _ r.2 (self_mem_ballP _))
    rw [ho, E_center]
  refine ⟨σ, hσr, ?_⟩
  intro r hr p
  have hσr' : σ r = (τ ⟨r, hr⟩).1 := hσr ⟨r, hr⟩
  constructor
  · intro hcoll
    have hpb : p ∈ ballP inc r := mem_ballP.2 (Or.inr hcoll)
    have hpA : p ∈ bigA inc R := mem_biUnion.2 ⟨r, hr, hpb⟩
    have ho : own hpA = ⟨r, hr⟩ := Subtype.ext (own_eq hR hpA hr hpb)
    have hm : σ p ∈ ballL inc (τ ⟨r, hr⟩).1 := by
      rw [hσA p hpA, ho]; exact E_mem hdig hP hL τ _ hpb
    rcases mem_ballL.1 hm with h | h
    · exact absurd (σ.injective (h.trans hσr'.symm)) (Ne.symm hcoll.1)
    · rw [hσr']; exact h
  · intro hconc
    have hm : σ p ∈ ballL inc (τ ⟨r, hr⟩).1 := mem_ballL.2 (Or.inr (hσr' ▸ hconc))
    have hpA : p ∈ bigA inc R := by
      by_contra hpA
      exact hσB p hpA (mem_biUnion.2 ⟨_, (τ ⟨r, hr⟩).2, hm⟩)
    have hm' : σ p ∈ ballL inc (τ (own hpA)).1 := by rw [hσA p hpA]; exact E_mem hdig hP hL τ _ (own_spec hpA)
    have ho : own hpA = ⟨r, hr⟩ := τ.injective (tau_eq_of_mem hS hm' hm)
    have hpb : p ∈ ballP inc r := by have := own_spec hpA; rw [ho] at this; exact this
    rcases mem_ballP.1 hpb with h | h
    · subst h; exact absurd rfl hconc.1
    · exact h

end Glue

end BipartiteDD.HexagonD7
