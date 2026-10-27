import BipartiteDD.LeanAll.Typed

/-! # Typed levels with relaxed freed sets (research/d15D7b/RELAXED.md)

`Typed.THyp` with (H1) relaxed: a freed element may be co-adjacent to one other freed element of its transition (its
partner, `RTHyp.r1`), provided the pair is served by hubs (`RTHyp.r1h`): a point-side hub whose slots are `σ r` in the
target level and an element adjacent to the partner `s` in the source level, and a line-side hub whose slots are `r`
in the source level and an element adjacent to `σ s` in the target level. The proof is that of `Typed.THyp.cross`:
where the covering element is the partner, the route goes through the hub (`1 + 1 + 4`); where two neighbours of an
element could both be images of freed elements, a third neighbour is used (`Base3`: three neighbours of every
element). The graph `X`, the colouring and the degree counts are those of `Typed`. -/

namespace BipartiteDD.LeanAll.RTyped

open SimpleGraph Finset BipartiteDD.Hexagon BipartiteDD.HexagonD7 BipartiteDD.LeanAll.Typed
open scoped Classical

set_option linter.unusedSectionVars false

variable {P L V U : Type*}

/-- Three neighbours of every element. -/
structure Base3 (inc : P → L → Prop) : Prop where
  base : Base inc
  p3 : ∀ p, ∃ l1 l2 l3, l1 ≠ l2 ∧ l1 ≠ l3 ∧ l2 ≠ l3 ∧ inc p l1 ∧ inc p l2 ∧ inc p l3
  l3 : ∀ l, ∃ p1 p2 p3, p1 ≠ p2 ∧ p1 ≠ p3 ∧ p2 ≠ p3 ∧ inc p1 l ∧ inc p2 l ∧ inc p3 l

theorem Base3.three {inc : P → L → Prop} (hB : Base3 inc) (x : P ⊕ L) :
    ∃ y1 y2 y3, y1 ≠ y2 ∧ y1 ≠ y3 ∧ y2 ≠ y3 ∧ (Hexagon.incGraph inc).Adj x y1 ∧ (Hexagon.incGraph inc).Adj x y2 ∧
      (Hexagon.incGraph inc).Adj x y3 := by
  rcases x with p | l
  · obtain ⟨l1, l2, l3, h12, h13, h23, i1, i2, i3⟩ := hB.p3 p
    exact ⟨.inr l1, .inr l2, .inr l3, by simpa using h12, by simpa using h13, by simpa using h23,
      Hexagon.incGraph_adj_inl_inr.2 i1, Hexagon.incGraph_adj_inl_inr.2 i2, Hexagon.incGraph_adj_inl_inr.2 i3⟩
  · obtain ⟨p1, p2, p3, h12, h13, h23, i1, i2, i3⟩ := hB.l3 l
    exact ⟨.inl p1, .inl p2, .inl p3, by simpa using h12, by simpa using h13, by simpa using h23,
      Hexagon.incGraph_adj_inr_inl.2 i1, Hexagon.incGraph_adj_inr_inl.2 i2, Hexagon.incGraph_adj_inr_inl.2 i3⟩

variable {inc : P → L → Prop} {j : ℕ} {τ : ZMod (2 * j + 1) → Bool}
  {σ : ZMod (2 * j + 1) → ℕ → (P ⊕ L) ≃ (P ⊕ L)} {R : ZMod (2 * j + 1) → ℕ → Set (P ⊕ L)}
  {slotV : V → ZMod (2 * j + 1) → P ⊕ L} {slotU : U → ZMod (2 * j + 1) → P ⊕ L} {NS : V → U → Prop}

/-- The hypotheses. -/
structure RTHyp (inc : P → L → Prop) (j : ℕ) (τ : ZMod (2 * j + 1) → Bool)
    (σ : ZMod (2 * j + 1) → ℕ → (P ⊕ L) ≃ (P ⊕ L)) (R : ZMod (2 * j + 1) → ℕ → Set (P ⊕ L))
    (slotV : V → ZMod (2 * j + 1) → P ⊕ L) (slotU : U → ZMod (2 * j + 1) → P ⊕ L) (NS : V → U → Prop) : Prop where
  base : Base3 inc
  maps : ∀ i (k : ℕ), 1 ≤ k → k ≤ j → ∀ x, colE x = τ i → colE (σ i k x) = !τ (i + k)
  onto : ∀ i (k : ℕ), 1 ≤ k → k ≤ j → ∀ y, colE y = !τ (i + k) → colE ((σ i k).symm y) = τ i
  rA : ∀ i (k : ℕ), 1 ≤ k → k ≤ j → ∀ x ∈ R i k, colE x = τ i
  r1 : ∀ i (k : ℕ), 1 ≤ k → k ≤ j → ∀ r ∈ R i k, ∀ s ∈ R i k, ∀ s' ∈ R i k, Co inc r s → Co inc r s' → s = s'
  r1h : ∀ i (k : ℕ), 1 ≤ k → k ≤ j → ∀ r ∈ R i k, ∀ s ∈ R i k, Co inc r s →
    (∃ u, slotU u (i + k) = σ i k r ∧ (Hexagon.incGraph inc).Adj (slotU u i) s) ∧
    (∃ v, slotV v i = r ∧ (Hexagon.incGraph inc).Adj (slotV v (i + k)) (σ i k s))
  r2 : ∀ i (k : ℕ), 1 ≤ k → k ≤ j → ∀ r ∈ R i k, ∀ x, Co inc r x ↔ Co inc (σ i k r) (σ i k x)
  slotA : ∀ v i, colE (slotV v i) = τ i
  slotB : ∀ u i, colE (slotU u i) = !τ i
  r3V : ∀ v v', (∃ i, Reach (Hexagon.incGraph inc) (slotV v i) (slotV v' i) 4) ∨ Reach (hubGraph NS) (.inl v) (.inl v') 6
  r3U : ∀ u u', (∃ i, Reach (Hexagon.incGraph inc) (slotU u i) (slotU u' i) 4) ∨ Reach (hubGraph NS) (.inr u) (.inr u') 6

section Dist

variable (H : RTHyp inc j τ σ R slotV slotU NS)
include H

theorem RTHyp.adj_shift {x : P ⊕ L} {i : ZMod (2 * j + 1)} {k : ℕ} (hk1 : 1 ≤ k) (hkj : k ≤ j) (hx : colE x = τ i)
    (hR : x ∉ R i k) : (X inc j τ σ R slotV slotU NS).Adj (.inl (x, i)) (.inl (σ i k x, i + k)) :=
  (SimpleGraph.fromRel_adj _ _ _).2 ⟨fun h => shift_ne i hk1 hkj (congrArg Prod.snd (Sum.inl_injective h)).symm,
    Or.inl (Or.inr ⟨k, hk1, hkj, rfl, hx, hR, rfl⟩)⟩

theorem RTHyp.level (x y : P ⊕ L) (i : ZMod (2 * j + 1)) :
    Reach (X inc j τ σ R slotV slotU NS) (.inl (x, i)) (.inl (y, i)) 6 :=
  (H.base.base.all6 x y).map (lvl inc j τ σ R slotV slotU NS i)

theorem RTHyp.adj_slotV (v : V) (i : ZMod (2 * j + 1)) :
    (X inc j τ σ R slotV slotU NS).Adj (.inr (.inl v)) (.inl (slotV v i, i)) :=
  (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl rfl⟩

theorem RTHyp.adj_slotU (u : U) (i : ZMod (2 * j + 1)) :
    (X inc j τ σ R slotV slotU NS).Adj (.inr (.inr u)) (.inl (slotU u i, i)) :=
  (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl rfl⟩

/-- A freed element reaches every `A`-element of the target level within `6`. -/
theorem RTHyp.freed {r b : P ⊕ L} {i : ZMod (2 * j + 1)} {k : ℕ} (hk1 : 1 ≤ k) (hkj : k ≤ j) (hr : r ∈ R i k)
    (hb : colE b = τ (i + k)) :
    Reach (X inc j τ σ R slotV slotU NS) (.inl (r, i)) (.inl (b, i + k)) 6 := by
  have hrA := H.rA i k hk1 hkj r hr
  have hσr := H.maps i k hk1 hkj r hrA
  obtain ⟨u', hco, hreach⟩ := H.base.base.coverE (u := σ i k r) (x := b) (by rw [hσr, hb]; simp)
  set p' := (σ i k).symm u' with hp'
  have hσp : σ i k p' = u' := by simp [hp']
  have hp'A : colE p' = τ i := H.onto i k hk1 hkj u' (by rw [← hco.colE_eq, hσr])
  have hco' : Co inc r p' := (H.r2 i k hk1 hkj r hr p').2 (by rw [hσp]; exact hco)
  by_cases hp'R : p' ∈ R i k
  · -- the partner: the line-side hub of `r` has its target slot next to `σ p' = u'`
    obtain ⟨v, hv1, hv2⟩ := (H.r1h i k hk1 hkj r hr p' hp'R hco').2
    rw [hσp] at hv2
    have h1 := Reach.adj (H.adj_slotV v i)
    rw [hv1] at h1
    have h2 := Reach.adj (H.adj_slotV v (i + k))
    have h3 := ((Reach.adj hv2).trans hreach).map (lvl inc j τ σ R slotV slotU NS (i + k))
    exact ((h1.symm.trans h2).trans h3).mono (by norm_num)
  · have h1 := hco'.reach.map (lvl inc j τ σ R slotV slotU NS i)
    have h2 := Reach.adj (H.adj_shift hk1 hkj hp'A hp'R)
    have h3 := hreach.map (lvl inc j τ σ R slotV slotU NS (i + k))
    rw [hσp] at h2
    exact ((h1.trans h2).trans h3).mono (by norm_num)

/-- Two vertices in levels `i` and `i + k`. -/
theorem RTHyp.cross (x y : P ⊕ L) (i : ZMod (2 * j + 1)) {k : ℕ} (hk1 : 1 ≤ k) (hkj : k ≤ j) :
    Reach (X inc j τ σ R slotV slotU NS) (.inl (x, i)) (.inl (y, i + k)) 7 := by
  by_cases hxA : colE x = τ i
  · by_cases hxR : x ∈ R i k
    · by_cases hyA : colE y = τ (i + k)
      · exact (H.freed hk1 hkj hxR hyA).mono (by norm_num)
      · obtain ⟨c, -, -, hc, -⟩ := H.base.base.two y
        have hcA : colE c = τ (i + k) := by
          have := colE_adj hc
          cases h1 : colE y <;> cases h2 : colE c <;> cases h3 : τ (i + k) <;> simp_all
        have h1 := H.freed hk1 hkj hxR hcA
        have h2 := (lvl inc j τ σ R slotV slotU NS (i + k)).map_rel hc.symm
        exact h1.trans (Reach.adj h2)
    · exact (Reach.adj (H.adj_shift hk1 hkj hxA hxR)).trans (H.level _ y _)
  · have hxB : colE x = !τ i := by cases h1 : colE x <;> cases h2 : τ i <;> simp_all
    by_cases hyA : colE y = τ (i + k)
    · -- some neighbour of `y` is not the image of a freed element (three neighbours, at most two such images)
      obtain ⟨w1, w2, w3, h12, h13, h23, hw1, hw2, hw3⟩ := H.base.three y
      have hwB : ∀ z, (Hexagon.incGraph inc).Adj y z → colE z = !τ (i + k) := fun z hz => by
        have := colE_adj hz
        cases h1 : colE y <;> cases h2 : colE z <;> cases h3 : τ (i + k) <;> simp_all
      have hco : ∀ z z', z ≠ z' → (Hexagon.incGraph inc).Adj y z → (Hexagon.incGraph inc).Adj y z' →
          (σ i k).symm z ∈ R i k → Co inc ((σ i k).symm z) ((σ i k).symm z') := fun z z' hne hz hz' hR =>
        (H.r2 i k hk1 hkj _ hR _).2 (by simp only [Equiv.apply_symm_apply]; exact ⟨hne, y, hz.symm, hz'⟩)
      have hinj : ∀ z z', (σ i k).symm z = (σ i k).symm z' → z = z' := fun z z' h => (σ i k).symm.injective h
      have hgood : ∃ z, (Hexagon.incGraph inc).Adj y z ∧ (σ i k).symm z ∉ R i k := by
        by_contra hcon
        push_neg at hcon
        have e := H.r1 i k hk1 hkj _ (hcon w1 hw1) _ (hcon w2 hw2) _ (hcon w3 hw3)
          (hco w1 w2 h12 hw1 hw2 (hcon w1 hw1)) (hco w1 w3 h13 hw1 hw3 (hcon w1 hw1))
        exact h23 (hinj _ _ e)
      obtain ⟨z, hz, hzR⟩ := hgood
      have hzA : colE ((σ i k).symm z) = τ i := H.onto i k hk1 hkj z (hwB z hz)
      have h1 := (H.base.base.odd (x := x) (y := (σ i k).symm z) (by rw [hxB, hzA]; simp)).map
        (lvl inc j τ σ R slotV slotU NS i)
      have h2 := Reach.adj (H.adj_shift hk1 hkj hzA hzR)
      rw [Equiv.apply_symm_apply] at h2
      have h3 := (lvl inc j τ σ R slotV slotU NS (i + k)).map_rel hz.symm
      exact (h1.trans h2).trans (Reach.adj h3)
    · have hyB : colE y = !τ (i + k) := by cases h1 : colE y <;> cases h2 : τ (i + k) <;> simp_all
      set r := (σ i k).symm y with hr
      have hrA : colE r = τ i := H.onto i k hk1 hkj y hyB
      have hσr : σ i k r = y := by simp [hr]
      by_cases hrR : r ∈ R i k
      · obtain ⟨p', hco, hreach⟩ := H.base.base.coverE (u := r) (x := x) (by rw [hrA, hxB]; simp)
        by_cases hp'R : p' ∈ R i k
        · -- the partner: the point-side hub of `σ r = y` has its source slot next to `p'`
          obtain ⟨u, hu1, hu2⟩ := (H.r1h i k hk1 hkj r hrR p' hp'R hco).1
          rw [hσr] at hu1
          have h1 := (hreach.symm.trans (Reach.adj hu2.symm)).map (lvl inc j τ σ R slotV slotU NS i)
          have h2 := (Reach.adj (H.adj_slotU u i)).symm
          have h3 := Reach.adj (H.adj_slotU u (i + k))
          rw [hu1] at h3
          exact ((h1.trans h2).trans h3).mono (by norm_num)
        · have hp'A : colE p' = τ i := by rw [← hco.colE_eq, hrA]
          have hco' := (H.r2 i k hk1 hkj r hrR p').1 hco
          rw [hσr] at hco'
          have h1 := hreach.symm.map (lvl inc j τ σ R slotV slotU NS i)
          have h2 := Reach.adj (H.adj_shift hk1 hkj hp'A hp'R)
          have h3 := hco'.reach.symm.map (lvl inc j τ σ R slotV slotU NS (i + k))
          exact ((h1.trans h2).trans h3).mono (by norm_num)
      · have h1 := (H.base.base.odd (x := x) (y := r) (by rw [hxB, hrA]; simp)).map
          (lvl inc j τ σ R slotV slotU NS i)
        have h2 := Reach.adj (H.adj_shift hk1 hkj hrA hrR)
        rw [hσr] at h2
        exact (h1.trans h2).mono (by norm_num)

theorem RTHyp.levels (x y : P ⊕ L) (i i' : ZMod (2 * j + 1)) :
    Reach (X inc j τ σ R slotV slotU NS) (.inl (x, i)) (.inl (y, i')) 7 := by
  by_cases h : i = i'
  · subst h; exact (H.level x y i).mono (by norm_num)
  · rcases shift_or h with ⟨k, hk1, hkj, rfl⟩ | ⟨k, hk1, hkj, rfl⟩
    · exact H.cross x y i hk1 hkj
    · exact (H.cross y x i' hk1 hkj).symm

theorem RTHyp.hubs (a b : V ⊕ U) : Reach (X inc j τ σ R slotV slotU NS) (.inr a) (.inr b) 7 := by
  rcases a with v | u <;> rcases b with v' | u'
  · rcases H.r3V v v' with ⟨i, h⟩ | h
    · have h1 := Reach.adj (H.adj_slotV v i)
      have h2 := h.map (lvl inc j τ σ R slotV slotU NS i)
      have h3 := (Reach.adj (H.adj_slotV v' i)).symm
      exact ((h1.trans h2).trans h3).mono (by norm_num)
    · exact (h.map (hubHom inc j τ σ R slotV slotU NS)).mono (by norm_num)
  · have h1 := Reach.adj (H.adj_slotV v 0)
    have h2 := (H.base.base.odd (x := slotV v 0) (y := slotU u' 0) (by rw [H.slotA, H.slotB]; simp)).map
      (lvl inc j τ σ R slotV slotU NS 0)
    have h3 := (Reach.adj (H.adj_slotU u' 0)).symm
    exact (h1.trans h2).trans h3
  · have h1 := Reach.adj (H.adj_slotU u 0)
    have h2 := (H.base.base.odd (x := slotU u 0) (y := slotV v' 0) (by rw [H.slotA, H.slotB]; simp)).map
      (lvl inc j τ σ R slotV slotU NS 0)
    have h3 := (Reach.adj (H.adj_slotV v' 0)).symm
    exact (h1.trans h2).trans h3
  · rcases H.r3U u u' with ⟨i, h⟩ | h
    · have h1 := Reach.adj (H.adj_slotU u i)
      have h2 := h.map (lvl inc j τ σ R slotV slotU NS i)
      have h3 := (Reach.adj (H.adj_slotU u' i)).symm
      exact ((h1.trans h2).trans h3).mono (by norm_num)
    · exact (h.map (hubHom inc j τ σ R slotV slotU NS)).mono (by norm_num)

theorem RTHyp.reach7 (a b : Typed.Vtx P L V U j) : Reach (X inc j τ σ R slotV slotU NS) a b 7 := by
  rcases a with ⟨x, i⟩ | a <;> rcases b with ⟨y, i'⟩ | b
  · exact H.levels x y i i'
  · rcases b with v | u
    · exact ((Reach.adj (H.adj_slotV v i)).trans (H.level _ x i)).symm
    · exact ((Reach.adj (H.adj_slotU u i)).trans (H.level _ x i)).symm
  · rcases a with v | u
    · exact (Reach.adj (H.adj_slotV v i')).trans (H.level _ y i')
    · exact (Reach.adj (H.adj_slotU u i')).trans (H.level _ y i')
  · exact H.hubs a b

/-- **The distance bound.** -/
theorem RTHyp.ediam_le : (X inc j τ σ R slotV slotU NS).ediam ≤ 7 :=
  SimpleGraph.ediam_le_iff.2 fun a b => (H.reach7 a b).edist_le

end Dist

/-! ## Colouring, degrees, order (as in `Typed`) -/

section Degree

variable (H : RTHyp inc j τ σ R slotV slotU NS)
include H

theorem RTHyp.rel_col {a b : Typed.Vtx P L V U j} (h : rel inc j τ σ R slotV slotU NS a b) : col τ a ≠ col τ b := by
  rcases a with ⟨x, i⟩ | v | u <;> rcases b with ⟨y, i'⟩ | v' | u'
  · rcases h with ⟨hxy, rfl⟩ | ⟨k, hk1, hkj, rfl, hx, -, rfl⟩
    · have := colE_adj hxy
      simp only [Typed.col]
      cases h1 : colE x <;> cases h2 : colE y <;> cases h3 : τ i <;> simp_all
    · have := H.maps i k hk1 hkj x hx
      simp only [Typed.col, hx, this]
      cases τ (i + k) <;> simp
  · exact absurd h id
  · exact absurd h id
  · have h' : y = slotV v i' := h
    simp [Typed.col, h', H.slotA]
  · exact absurd h id
  · simp [Typed.col]
  · have h' : y = slotU u i' := h
    simp only [Typed.col, h', H.slotB]
    cases τ i' <;> simp
  · exact absurd h id
  · exact absurd h id

theorem RTHyp.colorable : (X inc j τ σ R slotV slotU NS).Colorable 2 :=
  ⟨Coloring.mk (col τ) fun {a b} h => by
    rcases (SimpleGraph.fromRel_adj _ _ _).1 h with ⟨-, h' | h'⟩
    · exact H.rel_col h'
    · exact (H.rel_col h').symm⟩

variable [Fintype P] [Fintype L] [Fintype V] [Fintype U] {q : ℕ}

theorem RTHyp.deg_A (hdeg : ∀ x : P ⊕ L, (univ.filter ((Hexagon.incGraph inc).Adj x)).card ≤ q + 1)
    (hSV : ∀ i x, (univ.filter (fun v => slotV v i = x)).card ≤ ((Finset.Icc 1 j).filter (fun k => x ∈ R i k)).card)
    {x : P ⊕ L} {i : ZMod (2 * j + 1)} (hxA : colE x = τ i) :
    ((X inc j τ σ R slotV slotU NS).neighborSet (.inl (x, i))).ncard ≤ q + 1 + j := by
  set A : Finset (Typed.Vtx P L V U j) := (univ.filter ((Hexagon.incGraph inc).Adj x)).image (fun y => .inl (y, i))
  set B : Finset (Typed.Vtx P L V U j) :=
    ((Finset.Icc 1 j).filter (fun k => x ∉ R i k)).image (fun k : ℕ => .inl (σ i k x, i + k))
  set C : Finset (Typed.Vtx P L V U j) := (univ.filter (fun v => slotV v i = x)).image (fun v => .inr (.inl v))
  have hA : A.card ≤ q + 1 := card_image_le.trans (hdeg x)
  have hBC : B.card + C.card ≤ j := by
    have h1 : B.card ≤ ((Finset.Icc 1 j).filter (fun k => x ∉ R i k)).card := card_image_le
    have h2 : C.card ≤ ((Finset.Icc 1 j).filter (fun k => x ∈ R i k)).card := card_image_le.trans (hSV i x)
    have h3 := Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 j) (fun k => x ∈ R i k)
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at h3
    omega
  refine (ncard_le_of_subset (A ∪ B ∪ C) fun b hb => ?_).trans
    ((card_union_le _ _).trans (by have := card_union_le A B; omega))
  rcases (SimpleGraph.fromRel_adj _ _ _).1 hb with ⟨-, h | h⟩
  · rcases b with ⟨y, i'⟩ | v | u
    · rcases h with ⟨hxy, rfl⟩ | ⟨k, hk1, hkj, rfl, -, hR, rfl⟩
      · exact mem_union_left _ (mem_union_left _ (mem_image.2 ⟨y, by simpa using hxy, rfl⟩))
      · exact mem_union_left _ (mem_union_right _ (mem_image.2 ⟨k, by simp [hk1, hkj, hR], rfl⟩))
    · exact absurd h id
    · exact absurd h id
  · rcases b with ⟨y, i'⟩ | v | u
    · rcases h with ⟨hxy, rfl⟩ | ⟨k, hk1, hkj, rfl, hy, -, rfl⟩
      · exact mem_union_left _ (mem_union_left _ (mem_image.2 ⟨y, by simpa using hxy.symm, rfl⟩))
      · have := H.maps i' k hk1 hkj y hy
        rw [hxA] at this
        cases h1 : τ (i' + k) <;> rw [h1] at this <;> simp at this
    · have h' : x = slotV v i := h
      exact mem_union_right _ (mem_image.2 ⟨v, by simp [h'], rfl⟩)
    · have h' : x = slotU u i := h
      have := H.slotB u i
      rw [← h', hxA] at this
      cases h1 : τ i <;> rw [h1] at this <;> simp at this

theorem RTHyp.deg_B (hdeg : ∀ x : P ⊕ L, (univ.filter ((Hexagon.incGraph inc).Adj x)).card ≤ q + 1)
    (hSU : ∀ i x, (univ.filter (fun u => slotU u i = x)).card ≤
      ((Finset.Icc 1 j).filter (fun k : ℕ => (σ (i - (k : ZMod (2 * j + 1))) k).symm x ∈ R (i - (k : ZMod (2 * j + 1))) k)).card)
    {x : P ⊕ L} {i : ZMod (2 * j + 1)} (hxB : colE x ≠ τ i) :
    ((X inc j τ σ R slotV slotU NS).neighborSet (.inl (x, i))).ncard ≤ q + 1 + j := by
  set A : Finset (Typed.Vtx P L V U j) := (univ.filter ((Hexagon.incGraph inc).Adj x)).image (fun y => .inl (y, i))
  set B : Finset (Typed.Vtx P L V U j) :=
    ((Finset.Icc 1 j).filter (fun k : ℕ => (σ (i - (k : ZMod (2 * j + 1))) k).symm x ∉ R (i - (k : ZMod (2 * j + 1))) k)).image
      (fun k : ℕ => .inl ((σ (i - (k : ZMod (2 * j + 1))) k).symm x, i - (k : ZMod (2 * j + 1))))
  set C : Finset (Typed.Vtx P L V U j) := (univ.filter (fun u => slotU u i = x)).image (fun u => .inr (.inr u))
  have hA : A.card ≤ q + 1 := card_image_le.trans (hdeg x)
  have hBC : B.card + C.card ≤ j := by
    have h1 : B.card ≤ ((Finset.Icc 1 j).filter (fun k : ℕ => (σ (i - (k : ZMod (2 * j + 1))) k).symm x ∉ R (i - (k : ZMod (2 * j + 1))) k)).card :=
      card_image_le
    have h2 : C.card ≤ ((Finset.Icc 1 j).filter (fun k : ℕ => (σ (i - (k : ZMod (2 * j + 1))) k).symm x ∈
        R (i - (k : ZMod (2 * j + 1))) k)).card := card_image_le.trans (hSU i x)
    have h3 := Finset.card_filter_add_card_filter_not (s := Finset.Icc 1 j)
      (fun k : ℕ => (σ (i - (k : ZMod (2 * j + 1))) k).symm x ∈ R (i - (k : ZMod (2 * j + 1))) k)
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at h3
    omega
  refine (ncard_le_of_subset (A ∪ B ∪ C) fun b hb => ?_).trans
    ((card_union_le _ _).trans (by have := card_union_le A B; omega))
  rcases (SimpleGraph.fromRel_adj _ _ _).1 hb with ⟨-, h | h⟩
  · rcases b with ⟨y, i'⟩ | v | u
    · rcases h with ⟨hxy, rfl⟩ | ⟨k, hk1, hkj, rfl, hx, -, rfl⟩
      · exact mem_union_left _ (mem_union_left _ (mem_image.2 ⟨y, by simpa using hxy, rfl⟩))
      · exact absurd hx hxB
    · exact absurd h id
    · exact absurd h id
  · rcases b with ⟨y, i'⟩ | v | u
    · rcases h with ⟨hxy, rfl⟩ | ⟨k, hk1, hkj, rfl, hy, hR, rfl⟩
      · exact mem_union_left _ (mem_union_left _ (mem_image.2 ⟨y, by simpa using hxy.symm, rfl⟩))
      · have hi : i' + k - k = i' := by ring
        refine mem_union_left _ (mem_union_right _ (mem_image.2 ⟨k, ?_, ?_⟩))
        · simp only [mem_filter, Finset.mem_Icc, hi, Equiv.symm_apply_apply]
          exact ⟨⟨hk1, hkj⟩, hR⟩
        · simp only [hi, Equiv.symm_apply_apply]
    · have h' : x = slotV v i := h
      have := H.slotA v i
      rw [← h'] at this
      exact absurd this hxB
    · have h' : x = slotU u i := h
      exact mem_union_right _ (mem_image.2 ⟨u, by simp [h'], rfl⟩)

theorem RTHyp.deg_hubV (hNV : ∀ v, (univ.filter (NS v)).card ≤ q - j) (hjq : j ≤ q) (v : V) :
    ((X inc j τ σ R slotV slotU NS).neighborSet (.inr (.inl v))).ncard ≤ q + 1 + j := by
  set A : Finset (Typed.Vtx P L V U j) := univ.image (fun i : ZMod (2 * j + 1) => .inl (slotV v i, i))
  set B : Finset (Typed.Vtx P L V U j) := (univ.filter (NS v)).image (fun u => .inr (.inr u))
  have hA : A.card ≤ 2 * j + 1 := card_image_le.trans (by simp [ZMod.card])
  have hB : B.card ≤ q - j := card_image_le.trans (hNV v)
  refine (ncard_le_of_subset (A ∪ B) fun b hb => ?_).trans ((card_union_le _ _).trans (by omega))
  rcases (SimpleGraph.fromRel_adj _ _ _).1 hb with ⟨-, h | h⟩
  · rcases b with ⟨y, i⟩ | y | u
    · have h' : y = slotV v i := h
      exact mem_union_left _ (mem_image.2 ⟨i, mem_univ _, by rw [h']⟩)
    · exact absurd h id
    · have h' : NS v u := h
      exact mem_union_right _ (mem_image.2 ⟨u, by simpa using h', rfl⟩)
  · rcases b with ⟨y, i⟩ | y | y <;> exact absurd h id

theorem RTHyp.deg_hubU (hNU : ∀ u, (univ.filter (fun v => NS v u)).card ≤ q - j) (hjq : j ≤ q) (u : U) :
    ((X inc j τ σ R slotV slotU NS).neighborSet (.inr (.inr u))).ncard ≤ q + 1 + j := by
  set A : Finset (Typed.Vtx P L V U j) := univ.image (fun i : ZMod (2 * j + 1) => .inl (slotU u i, i))
  set B : Finset (Typed.Vtx P L V U j) := (univ.filter (fun v => NS v u)).image (fun v => .inr (.inl v))
  have hA : A.card ≤ 2 * j + 1 := card_image_le.trans (by simp [ZMod.card])
  have hB : B.card ≤ q - j := card_image_le.trans (hNU u)
  refine (ncard_le_of_subset (A ∪ B) fun b hb => ?_).trans ((card_union_le _ _).trans (by omega))
  rcases (SimpleGraph.fromRel_adj _ _ _).1 hb with ⟨-, h | h⟩
  · rcases b with ⟨y, i⟩ | y | y
    · have h' : y = slotU u i := h
      exact mem_union_left _ (mem_image.2 ⟨i, mem_univ _, by rw [h']⟩)
    · exact absurd h id
    · exact absurd h id
  · rcases b with ⟨y, i⟩ | v | y
    · exact absurd h id
    · have h' : NS v u := h
      exact mem_union_right _ (mem_image.2 ⟨v, by simpa using h', rfl⟩)
    · exact absurd h id

/-- **The theorem.** A bipartite graph of maximum degree `q + 1 + j` and diameter at most `7` on
`(2j + 1)(|P| + |L|) + |V| + |U|` vertices. -/
theorem RTHyp.exists_graph (hdeg : ∀ x : P ⊕ L, (univ.filter ((Hexagon.incGraph inc).Adj x)).card ≤ q + 1)
    (hSV : ∀ i x, (univ.filter (fun v => slotV v i = x)).card ≤ ((Finset.Icc 1 j).filter (fun k => x ∈ R i k)).card)
    (hSU : ∀ i x, (univ.filter (fun u => slotU u i = x)).card ≤
      ((Finset.Icc 1 j).filter (fun k : ℕ => (σ (i - (k : ZMod (2 * j + 1))) k).symm x ∈ R (i - (k : ZMod (2 * j + 1))) k)).card)
    (hNV : ∀ v, (univ.filter (NS v)).card ≤ q - j) (hNU : ∀ u, (univ.filter (fun v => NS v u)).card ≤ q - j)
    (hjq : j ≤ q) :
    ∃ G : SimpleGraph (Fin ((2 * j + 1) * (Fintype.card P + Fintype.card L) + Fintype.card V + Fintype.card U)),
      IsBipartiteDegDiam G (q + 1 + j) 7 := by
  have hX : IsBipartiteDegDiam (X inc j τ σ R slotV slotU NS) (q + 1 + j) 7 := by
    refine ⟨H.colorable, fun a => ?_, H.ediam_le⟩
    rcases a with ⟨x, i⟩ | v | u
    · by_cases hx : colE x = τ i
      · exact H.deg_A hdeg hSV hx
      · exact H.deg_B hdeg hSU hx
    · exact H.deg_hubV hNV hjq v
    · exact H.deg_hubU hNU hjq u
  have hcard : Fintype.card (Typed.Vtx P L V U j) =
      (2 * j + 1) * (Fintype.card P + Fintype.card L) + Fintype.card V + Fintype.card U := by
    simp only [Typed.Vtx, Fintype.card_sum, Fintype.card_prod, ZMod.card]; ring
  exact ⟨_, isBipartiteDegDiam_comap (Fintype.equivFinOfCardEq hcard) hX⟩

end Degree

end BipartiteDD.LeanAll.RTyped
