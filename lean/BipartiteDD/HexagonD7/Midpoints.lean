import BipartiteDD.HexagonD7.Mixed

/-! Diameter 7 from a generalized hexagon, part 12: freed sets whose midpoints are shared by at most two points
(THEOREM.md, Lemma 3 and Proposition 4).

Setting: no two points of `R` collinear, every point collinear with at most two points of `R`, and two points of `R`
have at most one common collinear point (true in every generalized hexagon); dually for the lines `τ r`. Call
`u, v ∈ R` *near* if they have a common collinear point (distance 4). Then the counts of Lemma 3' are determined by
the near graph on `R` and the sizes `|Γ₂(r)|`: a pair `{u, v}` is the type of exactly one point if `u, v` are near
and of none otherwise, `{u}` is the type of `|Γ₂(u)| - #(near neighbours of u)` points, larger sets of none, and `∅`
of the rest. So (`exists_r2_of_near`) if `τ` maps the near graph of `R` onto the near graph of the lines and
`|Γ₂(r)| = |Γ₂(τ r)|`, `|P| = |L|`, then `τ` extends to a `σ` with (R2). Proposition 4 is the case where `R` is a
pairwise opposite set plus pairwise opposite added points.

The counting is done once for an abstract set of centres `e : R → X` in a symmetric relation `Adj` on `X`
(`cntG_pair`, `cntG_single`, `sum_cntG`) and used for points (`Coll`) and for lines (`Conc`). -/

namespace BipartiteDD.HexagonD7

open Finset
open scoped Classical

set_option linter.unusedSectionVars false

section Generic

variable {X ι : Type*} [Fintype X] (Adj : X → X → Prop) (R : Finset ι) (e : R → X)

/-- The type of `x`: the centres adjacent to `x`. -/
noncomputable def typG (x : X) : Finset ι := R.filter (fun r => ∃ h : r ∈ R, Adj (e ⟨r, h⟩) x)

/-- The number of non-centres of type `T`. -/
noncomputable def cntG (T : Finset ι) : ℕ :=
  (univ.filter (fun x => x ∉ Set.range e ∧ typG Adj R e x = T)).card

/-- Two centres with a common neighbour. -/
def NearG (u v : R) : Prop := ∃ z, Adj (e u) z ∧ Adj (e v) z

variable {Adj R e}

theorem mem_typG {x : X} {r : ι} : r ∈ typG Adj R e x ↔ ∃ h : r ∈ R, Adj (e ⟨r, h⟩) x := by
  simp only [typG, mem_filter]
  exact ⟨fun h => h.2, fun ⟨hr, hc⟩ => ⟨hr, hr, hc⟩⟩

theorem typG_subset (x : X) : typG Adj R e x ⊆ R := filter_subset _ _

theorem card_typG_le (h3 : ∀ x (a b c : R), Adj (e a) x → Adj (e b) x → Adj (e c) x → a = b ∨ a = c ∨ b = c)
    (x : X) : (typG Adj R e x).card ≤ 2 := by
  by_contra hlt
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := two_lt_card_iff.1 (show 2 < (typG Adj R e x).card by omega)
  obtain ⟨ha', ha''⟩ := mem_typG.1 ha
  obtain ⟨hb', hb''⟩ := mem_typG.1 hb
  obtain ⟨hc', hc''⟩ := mem_typG.1 hc
  rcases h3 x ⟨a, ha'⟩ ⟨b, hb'⟩ ⟨c, hc'⟩ ha'' hb'' hc'' with h | h | h
  · exact hab (congrArg Subtype.val h)
  · exact hac (congrArg Subtype.val h)
  · exact hbc (congrArg Subtype.val h)

variable (hR1 : ∀ r s : R, ¬ Adj (e r) (e s))
  (h3 : ∀ x (a b c : R), Adj (e a) x → Adj (e b) x → Adj (e c) x → a = b ∨ a = c ∨ b = c)
  (hq : ∀ u v : R, u ≠ v → ∀ z z', Adj (e u) z → Adj (e v) z → Adj (e u) z' → Adj (e v) z' → z = z')

include hR1 in
theorem not_range_of_adj {r : R} {x : X} (h : Adj (e r) x) : x ∉ Set.range e := by
  rintro ⟨s, rfl⟩; exact hR1 r s h

include h3 in
theorem cntG_big {T : Finset ι} (hT : 3 ≤ T.card) : cntG Adj R e T = 0 := by
  rw [cntG, card_eq_zero, filter_eq_empty_iff]
  rintro x - ⟨-, hx⟩
  have := card_typG_le h3 x
  rw [hx] at this; omega

include hR1 h3 hq in
theorem cntG_pair (u v : R) (huv : u ≠ v) :
    cntG Adj R e {u.1, v.1} = if NearG Adj R e u v then 1 else 0 := by
  have hset : univ.filter (fun x => x ∉ Set.range e ∧ typG Adj R e x = {u.1, v.1}) =
      univ.filter (fun x => Adj (e u) x ∧ Adj (e v) x) := by
    ext x
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨-, hx⟩
      have hu : u.1 ∈ typG Adj R e x := by rw [hx]; simp
      have hv : v.1 ∈ typG Adj R e x := by rw [hx]; simp
      obtain ⟨_, hu'⟩ := mem_typG.1 hu
      obtain ⟨_, hv'⟩ := mem_typG.1 hv
      exact ⟨hu', hv'⟩
    · rintro ⟨hu, hv⟩
      refine ⟨not_range_of_adj hR1 hu, ?_⟩
      have hsub : ({u.1, v.1} : Finset ι) ⊆ typG Adj R e x := by
        intro r hr
        rcases mem_insert.1 hr with rfl | hr
        · exact mem_typG.2 ⟨u.2, hu⟩
        · rw [mem_singleton.1 hr]; exact mem_typG.2 ⟨v.2, hv⟩
      have hc : ({u.1, v.1} : Finset ι).card = 2 := card_pair (fun h => huv (Subtype.ext h))
      exact (eq_of_subset_of_card_le hsub (by rw [hc]; exact card_typG_le h3 x)).symm
  rw [cntG, hset]
  split_ifs with hn
  · obtain ⟨z, hz⟩ := hn
    rw [card_eq_one]
    refine ⟨z, ?_⟩
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun hx => hq u v huv x z hx.1 hx.2 hz.1 hz.2, fun h => h ▸ hz⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro x _ hx; exact hn ⟨x, hx⟩

include hR1 h3 hq in
theorem cntG_single (u : R) :
    cntG Adj R e {u.1} + (univ.filter (fun v : R => v ≠ u ∧ NearG Adj R e u v)).card =
      (univ.filter (Adj (e u))).card := by
  rw [← card_filter_add_card_filter_not (s := univ.filter (Adj (e u))) (fun x => typG Adj R e x = {u.1})]
  congr 1
  · rw [cntG, filter_filter]
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨-, hx⟩
      have : u.1 ∈ typG Adj R e x := by rw [hx]; exact mem_singleton_self _
      exact ⟨(mem_typG.1 this).2, hx⟩
    · rintro ⟨ha, hx⟩; exact ⟨not_range_of_adj hR1 ha, hx⟩
  · refine card_bij (fun v hv => Classical.choose (mem_filter.1 hv).2.2) ?_ ?_ ?_
    · intro v hv
      have hs := Classical.choose_spec (mem_filter.1 hv).2.2
      have hvu := (mem_filter.1 hv).2.1
      simp only [mem_filter, mem_univ, true_and]
      refine ⟨hs.1, fun hx => hvu ?_⟩
      have : v.1 ∈ typG Adj R e (Classical.choose (mem_filter.1 hv).2.2) := mem_typG.2 ⟨v.2, hs.2⟩
      rw [hx, mem_singleton] at this
      exact Subtype.ext this
    · intro v₁ hv₁ v₂ hv₂ h
      have hs₁ := Classical.choose_spec (mem_filter.1 hv₁).2.2
      have hs₂ := Classical.choose_spec (mem_filter.1 hv₂).2.2
      rw [h] at hs₁
      by_contra hne
      have h1 := (mem_filter.1 hv₁).2.1
      have h2 := (mem_filter.1 hv₂).2.1
      rcases h3 _ u v₁ v₂ hs₂.1 hs₁.2 hs₂.2 with h | h | h
      · exact h1 h.symm
      · exact h2 h.symm
      · exact hne h
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      have hu : u.1 ∈ typG Adj R e x := mem_typG.2 ⟨u.2, hx.1⟩
      obtain ⟨w, hw, hwu⟩ : ∃ w ∈ typG Adj R e x, w ≠ u.1 := by
        by_contra hall
        push Not at hall
        exact hx.2 (eq_singleton_iff_unique_mem.2 ⟨hu, hall⟩)
      obtain ⟨hwR, hwx⟩ := mem_typG.1 hw
      have hvu : (⟨w, hwR⟩ : R) ≠ u := fun h => hwu (congrArg Subtype.val h)
      have hnear : NearG Adj R e u ⟨w, hwR⟩ := ⟨x, hx.1, hwx⟩
      refine ⟨⟨w, hwR⟩, mem_filter.2 ⟨mem_univ _, hvu, hnear⟩, ?_⟩
      have hs := Classical.choose_spec (mem_filter.1 (mem_filter.2 ⟨mem_univ _, hvu, hnear⟩ :
        (⟨w, hwR⟩ : R) ∈ univ.filter (fun v : R => v ≠ u ∧ NearG Adj R e u v))).2.2
      exact hq u ⟨w, hwR⟩ (Ne.symm hvu) _ x hs.1 hs.2 hx.1 hwx

theorem sum_cntG :
    ∑ T ∈ R.powerset, cntG Adj R e T = (univ.filter (fun x => x ∉ Set.range e)).card := by
  rw [card_eq_sum_card_fiberwise (f := typG Adj R e) (t := R.powerset)
    (fun x _ => mem_powerset.2 (typG_subset x))]
  refine sum_congr rfl fun T _ => ?_
  rw [cntG, filter_filter]

end Generic

section Compare

variable {X X' ι : Type*} [Fintype X] [Fintype X'] {Adj : X → X → Prop} {Adj' : X' → X' → Prop}
  {R : Finset ι} {e : R → X} {e' : R → X'}

/-- Two centre sets with the same near graph and the same neighbourhood sizes have the same type counts. -/
theorem cntG_eq_of_near
    (hR1 : ∀ r s : R, ¬ Adj (e r) (e s))
    (h3 : ∀ x (a b c : R), Adj (e a) x → Adj (e b) x → Adj (e c) x → a = b ∨ a = c ∨ b = c)
    (hq : ∀ u v : R, u ≠ v → ∀ z z', Adj (e u) z → Adj (e v) z → Adj (e u) z' → Adj (e v) z' → z = z')
    (hR1' : ∀ r s : R, ¬ Adj' (e' r) (e' s))
    (h3' : ∀ x (a b c : R), Adj' (e' a) x → Adj' (e' b) x → Adj' (e' c) x → a = b ∨ a = c ∨ b = c)
    (hq' : ∀ u v : R, u ≠ v → ∀ z z', Adj' (e' u) z → Adj' (e' v) z → Adj' (e' u) z' → Adj' (e' v) z' → z = z')
    (hnear : ∀ u v, NearG Adj R e u v ↔ NearG Adj' R e' u v)
    (hc : ∀ r, (univ.filter (Adj (e r))).card = (univ.filter (Adj' (e' r))).card)
    (htot : (univ.filter (fun x => x ∉ Set.range e)).card = (univ.filter (fun x => x ∉ Set.range e')).card) :
    ∀ T ⊆ R, cntG Adj R e T = cntG Adj' R e' T := by
  have hne : ∀ T ⊆ R, T ≠ ∅ → cntG Adj R e T = cntG Adj' R e' T := by
    intro T hT hT0
    rcases Nat.lt_or_ge T.card 3 with hlt | hge
    · interval_cases hk : T.card
      · exact absurd (card_eq_zero.1 hk) hT0
      · obtain ⟨w, rfl⟩ := card_eq_one.1 hk
        have hw : w ∈ R := hT (mem_singleton_self w)
        have h1 := cntG_single hR1 h3 hq ⟨w, hw⟩
        have h2 := cntG_single hR1' h3' hq' ⟨w, hw⟩
        have hn : (univ.filter (fun v : R => v ≠ ⟨w, hw⟩ ∧ NearG Adj R e ⟨w, hw⟩ v)) =
            (univ.filter (fun v : R => v ≠ ⟨w, hw⟩ ∧ NearG Adj' R e' ⟨w, hw⟩ v)) := by
          ext v; simp only [mem_filter, mem_univ, true_and, hnear]
        rw [hn, hc] at h1
        dsimp only at h1 h2
        omega
      · obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 hk
        have ha : a ∈ R := hT (by simp)
        have hb : b ∈ R := hT (by simp)
        have hne : (⟨a, ha⟩ : R) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Subtype.val h)
        have e1 := cntG_pair hR1 h3 hq ⟨a, ha⟩ ⟨b, hb⟩ hne
        have e2 := cntG_pair hR1' h3' hq' ⟨a, ha⟩ ⟨b, hb⟩ hne
        simp only at e1 e2
        rw [e1, e2, hnear]
    · rw [cntG_big h3 hge, cntG_big h3' hge]
  intro T hT
  by_cases hT0 : T = ∅
  · subst hT0
    have s1 := sum_cntG (Adj := Adj) (R := R) (e := e)
    have s2 := sum_cntG (Adj := Adj') (R := R) (e := e')
    rw [← add_sum_erase _ _ (empty_mem_powerset R)] at s1 s2
    have hs : ∑ T ∈ R.powerset.erase ∅, cntG Adj R e T = ∑ T ∈ R.powerset.erase ∅, cntG Adj' R e' T :=
      sum_congr rfl fun T hT => hne T (mem_powerset.1 (mem_of_mem_erase hT)) (ne_of_mem_erase hT)
    omega
  · exact hne T hT hT0

end Compare

section Hexagon

variable {P L : Type*} [Fintype P] [Fintype L] {inc : P → L → Prop} {R : Finset P} {S : Finset L} (τ : R ≃ S)

/-- **Lemma 3 for midpoints of multiplicity two.** -/
theorem exists_r2_of_near (hR1 : ∀ r ∈ R, ∀ s ∈ R, ¬ Coll inc r s) (hS1 : ∀ a ∈ S, ∀ b ∈ S, ¬ Conc inc a b)
    (hR3 : ∀ p (a b c : R), Coll inc a p → Coll inc b p → Coll inc c p → a = b ∨ a = c ∨ b = c)
    (hS3 : ∀ l (a b c : R), Conc inc (τ a) l → Conc inc (τ b) l → Conc inc (τ c) l → a = b ∨ a = c ∨ b = c)
    (hqP : ∀ u v : R, u ≠ v → ∀ z z', Coll inc u z → Coll inc v z → Coll inc u z' → Coll inc v z' → z = z')
    (hqL : ∀ u v : R, u ≠ v → ∀ z z', Conc inc (τ u) z → Conc inc (τ v) z → Conc inc (τ u) z' →
      Conc inc (τ v) z' → z = z')
    (hnear : ∀ u v : R, (∃ z, Coll inc u z ∧ Coll inc v z) ↔ (∃ w, Conc inc (τ u) w ∧ Conc inc (τ v) w))
    (hc : ∀ r : R, (univ.filter (Coll inc r.1)).card = (univ.filter (Conc inc (τ r).1)).card)
    (hcard : Fintype.card P = Fintype.card L) :
    ∃ σ : P ≃ L, (∀ r : R, σ r.1 = (τ r).1) ∧ ∀ r ∈ R, ∀ p, Coll inc r p ↔ Conc inc (σ r) (σ p) := by
  let e : R → P := Subtype.val
  let e' : R → L := fun r => (τ r).1
  have hrange : ∀ p, p ∉ Set.range e ↔ p ∉ R := by
    intro p; simp [e]
  have hrange' : ∀ l, l ∉ Set.range e' ↔ l ∉ S := by
    intro l
    constructor
    · intro h hl; exact h ⟨τ.symm ⟨l, hl⟩, by simp [e']⟩
    · rintro h ⟨r, rfl⟩; exact h (τ r).2
  have htyp : ∀ p, typG (Coll inc) R e p = typP inc R p := by
    intro p; ext r; rw [mem_typG, mem_typP]
    exact ⟨fun ⟨h, hc⟩ => ⟨h, hc⟩, fun ⟨h, hc⟩ => ⟨h, hc⟩⟩
  have htyp' : ∀ l, typG (Conc inc) R e' l = typL inc τ l := fun l => rfl
  have key := cntG_eq_of_near (Adj := Coll inc) (Adj' := Conc inc) (R := R) (e := e) (e' := e')
    (fun r s => hR1 r.1 r.2 s.1 s.2) hR3 hqP
    (fun r s => hS1 _ (τ r).2 _ (τ s).2) hS3 hqL hnear hc (by
      have h1 : univ.filter (fun x => x ∉ Set.range e) = univ.filter (fun p => p ∉ R) := by
        ext p; simp only [mem_filter, mem_univ, true_and, hrange]
      have h2 : univ.filter (fun x => x ∉ Set.range e') = univ.filter (fun l => l ∉ S) := by
        ext l; simp only [mem_filter, mem_univ, true_and, hrange']
      have h3 : univ.filter (fun p => p ∉ R) = Rᶜ := by ext; simp
      have h4 : univ.filter (fun l => l ∉ S) = Sᶜ := by ext; simp
      rw [h1, h2, h3, h4, card_compl, card_compl, hcard]
      have := Fintype.card_congr τ
      rw [Fintype.card_coe, Fintype.card_coe] at this
      rw [this])
  refine (exists_r2_iff τ hR1 hS1).2 fun T hT => ?_
  have k := key T hT
  rw [cntG, cntG] at k
  convert k using 2
  · ext p; simp only [mem_filter, mem_univ, true_and, hrange, htyp]
  · ext l; simp only [mem_filter, mem_univ, true_and, hrange', htyp']

end Hexagon

end BipartiteDD.HexagonD7
