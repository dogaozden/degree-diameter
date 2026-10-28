import BipartiteDD.HexagonD7.Certificate

/-! Diameter 7 from a generalized hexagon, part 11: **Lemma 3** (freed points at distance 4) in counting form, the
duality case, and a certificate theorem for `H(q)` with `2j + 1` levels and mixed freed sets.

The *type* of a point `p` is the set of points of `R` collinear with `p`; the type of a line `l` is the set of
`r ∈ R` with `τ r` concurrent with `l`. If no two points of `R` are collinear and no two lines of `S` concurrent,
a bijection `τ : R ≃ S` extends to some `σ : P ≃ L` with (R2) iff for every `T ⊆ R` as many points outside `R` as
lines outside `S` have type `T` (`exists_r2_iff`). The midpoint condition of THEOREM.md, Lemma 3, is this count for
`|T| ≥ 2`; Lemma 2 is the case where all types have at most one element. The construction is one bijection per type
(`Equiv.ofFiberEquiv`).

`duality_r2`: the point part of a duality satisfies (R2) everywhere.

`certificate_mixed`: for every finite field `F`, `q = |F|`, `j ≤ q`, every `R`, `S`, `τ` with the counting
condition, hubs `V`, `U` with at most `j` per owner and a bipartite hub graph of degree `≤ q - j` in which two
same-side hubs are within 6 unless their owners (or the lines `τ` of their owners) are within 4 in `H(q)`, there
is a bipartite graph of maximum degree `q + 1 + j` and diameter `≤ 7` on `2(2j+1)(q+1)(q⁴+q²+1) + |V| + |U|`
vertices. -/

namespace BipartiteDD.HexagonD7

open SimpleGraph Finset BipartiteDD.Hexagon
open scoped Classical

set_option linter.unusedSectionVars false

section TypeCount

variable {P L : Type*} [Fintype P] [Fintype L] (inc : P → L → Prop) {R : Finset P} {S : Finset L} (τ : R ≃ S)

/-- The type of a point `p`: the points of `R` collinear with `p`. -/
noncomputable def typP (R : Finset P) (p : P) : Finset P := R.filter (fun r => Coll inc r p)

/-- The type of a line `l`: the points `r ∈ R` whose line `τ r` is concurrent with `l`. -/
noncomputable def typL (l : L) : Finset P := R.filter (fun r => ∃ h : r ∈ R, Conc inc (τ ⟨r, h⟩).1 l)

variable {inc}

theorem mem_typP {p r : P} : r ∈ typP inc R p ↔ r ∈ R ∧ Coll inc r p := by simp [typP]

theorem mem_typL {l : L} {r : P} : r ∈ typL inc τ l ↔ ∃ h : r ∈ R, Conc inc (τ ⟨r, h⟩).1 l := by
  simp only [typL, mem_filter]
  exact ⟨fun h => h.2, fun ⟨hr, hc⟩ => ⟨hr, hr, hc⟩⟩

theorem typP_subset (p : P) : typP inc R p ⊆ R := filter_subset _ _

theorem typL_subset (l : L) : typL inc τ l ⊆ R := filter_subset _ _

/-- **Lemma 3, counting form.** -/
theorem exists_r2_iff (hR1 : ∀ r ∈ R, ∀ s ∈ R, ¬ Coll inc r s) (hS1 : ∀ a ∈ S, ∀ b ∈ S, ¬ Conc inc a b) :
    (∃ σ : P ≃ L, (∀ r : R, σ r.1 = (τ r).1) ∧ ∀ r ∈ R, ∀ p, Coll inc r p ↔ Conc inc (σ r) (σ p)) ↔
    ∀ T ⊆ R, (univ.filter (fun p => p ∉ R ∧ typP inc R p = T)).card =
      (univ.filter (fun l => l ∉ S ∧ typL inc τ l = T)).card := by
  constructor
  · rintro ⟨σ, hστ, hσ⟩ T -
    have hσS : ∀ p, σ p ∈ S → p ∈ R := by
      intro p hp
      obtain ⟨r, hr⟩ := τ.surjective ⟨σ p, hp⟩
      have : σ r.1 = σ p := by rw [hστ, hr]
      rw [← σ.injective this]; exact r.2
    have hσR : ∀ p ∈ R, σ p ∈ S := fun p hp => by rw [hστ ⟨p, hp⟩]; exact (τ _).2
    have htyp : ∀ p, typL inc τ (σ p) = typP inc R p := by
      intro p; ext r
      rw [mem_typL, mem_typP]
      constructor
      · rintro ⟨hr, hc⟩; exact ⟨hr, (hσ r hr p).2 (by rw [hστ ⟨r, hr⟩]; exact hc)⟩
      · rintro ⟨hr, hc⟩; exact ⟨hr, by rw [← hστ ⟨r, hr⟩]; exact (hσ r hr p).1 hc⟩
    refine card_nbij' σ σ.symm ?_ ?_ ?_ ?_
    · intro p hp
      rw [mem_coe, mem_filter] at hp ⊢
      exact ⟨mem_univ _, fun h => hp.2.1 (hσS p h), (htyp p).trans hp.2.2⟩
    · intro l hl
      rw [mem_coe, mem_filter] at hl ⊢
      refine ⟨mem_univ _, fun h => hl.2.1 (by simpa using hσR _ h), ?_⟩
      rw [← htyp, Equiv.apply_symm_apply]; exact hl.2.2
    · intro p _; simp
    · intro l _; simp
  · intro hcount
    let fP : {p // p ∉ R} → Finset P := fun p => typP inc R p.1
    let gL : {l // l ∉ S} → Finset P := fun l => typL inc τ l.1
    have hc : ∀ T, Fintype.card {x // fP x = T} = Fintype.card {y // gL y = T} := by
      intro T
      rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun p => p ∉ R)
          (fun p => typP inc R p = T)),
        Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun l => l ∉ S)
          (fun l => typL inc τ l = T)),
        Fintype.card_subtype, Fintype.card_subtype]
      by_cases hT : T ⊆ R
      · exact hcount T hT
      · have h1 : univ.filter (fun p => p ∉ R ∧ typP inc R p = T) = ∅ := by
          refine filter_eq_empty_iff.2 fun p _ h => hT ?_
          rw [← h.2]; exact typP_subset p
        have h2 : univ.filter (fun l => l ∉ S ∧ typL inc τ l = T) = ∅ := by
          refine filter_eq_empty_iff.2 fun l _ h => hT ?_
          rw [← h.2]; exact typL_subset τ l
        rw [h1, h2, card_empty, card_empty]
    let e : ∀ T, {x // fP x = T} ≃ {y // gL y = T} := fun T => Fintype.equivOfCardEq (hc T)
    let g : {p // p ∉ R} ≃ {l // l ∉ S} := Equiv.ofFiberEquiv e
    have hg : ∀ x, typL inc τ (g x).1 = typP inc R x.1 := fun x => Equiv.ofFiberEquiv_map e x
    let σ : P ≃ L := ((Equiv.sumCompl (fun p => p ∈ R)).symm.trans (Equiv.sumCongr τ g)).trans
      (Equiv.sumCompl (fun l => l ∈ S))
    have hσR : ∀ r (hr : r ∈ R), σ r = (τ ⟨r, hr⟩).1 := by
      intro r hr
      simp only [σ, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hr, Equiv.sumCongr_apply,
        Sum.map_inl, Equiv.sumCompl_apply_inl]
    have hσN : ∀ p (hp : p ∉ R), σ p = (g ⟨p, hp⟩).1 := by
      intro p hp
      simp only [σ, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg hp, Equiv.sumCongr_apply,
        Sum.map_inr, Equiv.sumCompl_apply_inr]
    refine ⟨σ, fun r => hσR r.1 r.2, ?_⟩
    intro r hr p
    by_cases hp : p ∈ R
    · refine iff_of_false (hR1 r hr p hp) (hS1 _ ?_ _ ?_)
      · rw [hσR r hr]; exact (τ _).2
      · rw [hσR p hp]; exact (τ _).2
    · have ht := hg ⟨p, hp⟩
      rw [hσR r hr, hσN p hp]
      constructor
      · intro hc
        have hm : r ∈ typP inc R p := mem_typP.2 ⟨hr, hc⟩
        rw [← ht] at hm
        obtain ⟨hr', hc'⟩ := (mem_typL τ).1 hm
        exact hc'
      · intro hc
        have hm : r ∈ typL inc τ (g ⟨p, hp⟩).1 := (mem_typL τ).2 ⟨hr, hc⟩
        rw [ht] at hm
        exact (mem_typP.1 hm).2

/-- **Corollary (duality).** If `δP : P ≃ L` and `δL : L ≃ P` exchange points and lines preserving incidence, then
`δP` satisfies (R2) at every point, so every set `R` with (R1) can be freed. -/
theorem duality_r2 (δP : P ≃ L) (δL : L ≃ P) (hδ : ∀ p l, inc p l ↔ inc (δL l) (δP p)) (r p : P) :
    Coll inc r p ↔ Conc inc (δP r) (δP p) := by
  constructor
  · rintro ⟨hne, l, h1, h2⟩
    exact ⟨fun h => hne (δP.injective h), δL l, (hδ r l).1 h1, (hδ p l).1 h2⟩
  · rintro ⟨hne, x, h1, h2⟩
    refine ⟨fun h => hne (congrArg δP h), δL.symm x, ?_, ?_⟩
    · rw [hδ, Equiv.apply_symm_apply]; exact h1
    · rw [hδ, Equiv.apply_symm_apply]; exact h2

end TypeCount

section Certificate

variable {F : Type*} [Field F] [Fintype F]

theorem card_own_le {P W : Type*} [Fintype W] {R : Finset P} {j : ℕ} (own : W → R)
    (h : ∀ r, (univ.filter (fun w => own w = r)).card ≤ j) (r : P) :
    (univ.filter (fun w => (own w).1 = r)).card ≤ j := by
  by_cases hr : r ∈ R
  · have : univ.filter (fun w => (own w).1 = r) = univ.filter (fun w => own w = ⟨r, hr⟩) := by
      ext w; simp [Subtype.ext_iff]
    rw [this]; exact h _
  · have : univ.filter (fun w => (own w).1 = r) = ∅ :=
      filter_eq_empty_iff.2 fun w _ hw => hr (hw ▸ (own w).2)
    rw [this, card_empty]; exact Nat.zero_le _

/-- **Certificate for mixed freed sets and `2j + 1` levels.** -/
theorem certificate_mixed [Fintype (SPt F)] [Fintype (HLine F)] (j : ℕ) (hj : j ≤ Fintype.card F)
    (R : Finset (SPt F)) (S : Finset (HLine F)) (τ : R ≃ S)
    (hR1 : ∀ r ∈ R, ∀ s ∈ R, ¬ Coll hexInc r s) (hS1 : ∀ a ∈ S, ∀ b ∈ S, ¬ Conc hexInc a b)
    (hcount : ∀ T ⊆ R, (univ.filter (fun p => p ∉ R ∧ typP hexInc R p = T)).card =
      (univ.filter (fun l => l ∉ S ∧ typL hexInc τ l = T)).card)
    {V U : Type*} [Fintype V] [Fintype U] (ownV : V → R) (ownU : U → R)
    (hV : ∀ r, (univ.filter (fun v => ownV v = r)).card ≤ j)
    (hU : ∀ r, (univ.filter (fun u => ownU u = r)).card ≤ j)
    (NS : V → U → Prop)
    (hNV : ∀ v, (univ.filter (NS v)).card ≤ Fintype.card F - j)
    (hNU : ∀ u, (univ.filter (fun v => NS v u)).card ≤ Fintype.card F - j)
    (hV6 : ∀ v v', Reach (Hexagon.incGraph hexInc) (.inl (ownV v).1) (.inl (ownV v').1) 4 ∨
      Reach (hubGraph NS) (.inl v) (.inl v') 6)
    (hU6 : ∀ u u', Reach (Hexagon.incGraph hexInc) (.inr (τ (ownU u)).1) (.inr (τ (ownU u')).1) 4 ∨
      Reach (hubGraph NS) (.inr u) (.inr u') 6) :
    ∃ G : SimpleGraph (Fin (2 * (2 * j + 1) * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 +
        Fintype.card F ^ 4)) + Fintype.card V + Fintype.card U)),
      IsBipartiteDegDiam G (Fintype.card F + 1 + j) 7 := by
  set q := Fintype.card F with hqdef
  have hG := HexagonEven.genPolygonGraph_hexagon_even (F := F)
  have hP : ∀ p : SPt F, (univ.filter (hexInc p)).card = q + 1 := fun p => by
    rw [← HexagonEven.card_lines_through_even p, Nat.card_eq_fintype_card, Fintype.card_subtype]; rfl
  have hL : ∀ l : HLine F, (univ.filter (fun p => hexInc p l)).card = q + 1 := fun l => by
    rw [← card_points_hline l, Nat.card_eq_fintype_card, Fintype.card_subtype]; rfl
  have hcP : Fintype.card (SPt F) = (q + 1) * (1 + q ^ 2 + q ^ 4) := by
    rw [← card_spt_eq, Nat.card_eq_fintype_card]
  have hcL : Fintype.card (HLine F) = Fintype.card (SPt F) := by
    have := card_lines_eq (inc := hexInc (F := F)) (k := q + 1) (by omega)
      (fun p => by rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; exact hP p)
      (fun l => by rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; exact hL l)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this
    exact this
  obtain ⟨σ, hστ, hσ⟩ := (exists_r2_iff τ hR1 hS1).2 (fun T hT => by convert hcount T hT)
  have H : Hyp hexInc σ (↑R : Set (SPt F)) (fun v => (ownV v).1) (fun u => (ownU u).1) NS := {
    pl := pl_of_polygon hG,
    p2 := p2_of_polygon hG,
    l2 := l2_of_polygon hG,
    r1 := fun r hr s hs => hR1 r hr s hs,
    r2 := fun r hr p => hσ r hr p,
    ownV_mem := fun v => (ownV v).2,
    ownU_mem := fun u => (ownU u).2,
    r3V := hV6,
    r3U := fun u u' => by rw [hστ, hστ]; exact hU6 u u' }
  have main := exists_graph (q := q) (j := j) H (fun p => by convert (hP p).le)
    (fun l => by convert (hL l).le) (fun r => by convert card_own_le ownV (fun r => by convert hV r) r)
    (fun r => by convert card_own_le ownU (fun r => by convert hU r) r) (fun v => by convert hNV v)
    (fun u => by convert hNU u) hj
  have e : (2 * j + 1) * (Fintype.card (SPt F) + Fintype.card (HLine F)) + Fintype.card V +
      Fintype.card U = 2 * (2 * j + 1) * ((q + 1) * (1 + q ^ 2 + q ^ 4)) + Fintype.card V +
      Fintype.card U := by
    rw [hcL, hcP]; ring
  rw [e] at main
  exact main

end Certificate

end BipartiteDD.HexagonD7
