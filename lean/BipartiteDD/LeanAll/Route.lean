import BipartiteDD.LeanAll.Typed

/-! # Typed levels with a route hypothesis

The graph `Typed.X` (levels of an incidence structure, matchings `σ i k` from `A_i` to `B_{i+k}` with freed sets
`R i k`, hubs in free slots, a hub graph), with the per-transition hypotheses (H1), (H3) of `Typed.THyp` replaced by
the condition they are used for: every pair `(a, b)` of elements has a route `a → x → σ x → b` through a non-freed
`x ∈ A_i` of length at most `6` in the incidence graph (`RHyp.route`). Then two vertices of levels `i` and `i + k` are
within `1 + 6`. Everything else (colouring, degrees, hubs, order) is as in `Typed`; the proofs are those of `Typed`
with `RHyp` in place of `THyp`. Used for freed sets with collinear points (`Spread.lean`). -/

namespace BipartiteDD.LeanAll.Route

open SimpleGraph Finset BipartiteDD.Hexagon BipartiteDD.HexagonD7 BipartiteDD.LeanAll.Typed
open scoped Classical

set_option linter.unusedSectionVars false

variable {P L V U : Type*}

variable {inc : P → L → Prop} {j : ℕ} {τ : ZMod (2 * j + 1) → Bool}
  {σ : ZMod (2 * j + 1) → ℕ → (P ⊕ L) ≃ (P ⊕ L)} {R : ZMod (2 * j + 1) → ℕ → Set (P ⊕ L)}
  {slotV : V → ZMod (2 * j + 1) → P ⊕ L} {slotU : U → ZMod (2 * j + 1) → P ⊕ L} {NS : V → U → Prop}

/-- The hypotheses. -/
structure RHyp (inc : P → L → Prop) (j : ℕ) (τ : ZMod (2 * j + 1) → Bool)
    (σ : ZMod (2 * j + 1) → ℕ → (P ⊕ L) ≃ (P ⊕ L)) (R : ZMod (2 * j + 1) → ℕ → Set (P ⊕ L))
    (slotV : V → ZMod (2 * j + 1) → P ⊕ L) (slotU : U → ZMod (2 * j + 1) → P ⊕ L) (NS : V → U → Prop) : Prop where
  base : Base inc
  maps : ∀ i (k : ℕ), 1 ≤ k → k ≤ j → ∀ x, colE x = τ i → colE (σ i k x) = !τ (i + k)
  onto : ∀ i (k : ℕ), 1 ≤ k → k ≤ j → ∀ y, colE y = !τ (i + k) → colE ((σ i k).symm y) = τ i
  rA : ∀ i (k : ℕ), 1 ≤ k → k ≤ j → ∀ x ∈ R i k, colE x = τ i
  route : ∀ i (k : ℕ), 1 ≤ k → k ≤ j → ∀ a b : P ⊕ L, ∃ x, colE x = τ i ∧ x ∉ R i k ∧ ∃ m n, m + n ≤ 6 ∧
    Reach (Hexagon.incGraph inc) a x m ∧ Reach (Hexagon.incGraph inc) (σ i k x) b n
  slotA : ∀ v i, colE (slotV v i) = τ i
  slotB : ∀ u i, colE (slotU u i) = !τ i
  r3V : ∀ v v', (∃ i, Reach (Hexagon.incGraph inc) (slotV v i) (slotV v' i) 4) ∨ Reach (hubGraph NS) (.inl v) (.inl v') 6
  r3U : ∀ u u', (∃ i, Reach (Hexagon.incGraph inc) (slotU u i) (slotU u' i) 4) ∨ Reach (hubGraph NS) (.inr u) (.inr u') 6

section Dist

variable (H : RHyp inc j τ σ R slotV slotU NS)
include H

theorem RHyp.adj_shift {x : P ⊕ L} {i : ZMod (2 * j + 1)} {k : ℕ} (hk1 : 1 ≤ k) (hkj : k ≤ j) (hx : colE x = τ i)
    (hR : x ∉ R i k) : (X inc j τ σ R slotV slotU NS).Adj (.inl (x, i)) (.inl (σ i k x, i + k)) :=
  (SimpleGraph.fromRel_adj _ _ _).2 ⟨fun h => shift_ne i hk1 hkj (congrArg Prod.snd (Sum.inl_injective h)).symm,
    Or.inl (Or.inr ⟨k, hk1, hkj, rfl, hx, hR, rfl⟩)⟩

theorem RHyp.level (x y : P ⊕ L) (i : ZMod (2 * j + 1)) :
    Reach (X inc j τ σ R slotV slotU NS) (.inl (x, i)) (.inl (y, i)) 6 :=
  (H.base.all6 x y).map (lvl inc j τ σ R slotV slotU NS i)

/-- Two vertices in levels `i` and `i + k`. -/
theorem RHyp.cross (a b : P ⊕ L) (i : ZMod (2 * j + 1)) {k : ℕ} (hk1 : 1 ≤ k) (hkj : k ≤ j) :
    Reach (X inc j τ σ R slotV slotU NS) (.inl (a, i)) (.inl (b, i + k)) 7 := by
  obtain ⟨x, hxA, hxR, m, n, hmn, h1, h2⟩ := H.route i k hk1 hkj a b
  have e1 := h1.map (lvl inc j τ σ R slotV slotU NS i)
  have e2 := Reach.adj (H.adj_shift hk1 hkj hxA hxR)
  have e3 := h2.map (lvl inc j τ σ R slotV slotU NS (i + k))
  exact ((e1.trans e2).trans e3).mono (by omega)

theorem RHyp.levels (x y : P ⊕ L) (i i' : ZMod (2 * j + 1)) :
    Reach (X inc j τ σ R slotV slotU NS) (.inl (x, i)) (.inl (y, i')) 7 := by
  by_cases h : i = i'
  · subst h; exact (H.level x y i).mono (by norm_num)
  · rcases shift_or h with ⟨k, hk1, hkj, rfl⟩ | ⟨k, hk1, hkj, rfl⟩
    · exact H.cross x y i hk1 hkj
    · exact (H.cross y x i' hk1 hkj).symm

theorem RHyp.adj_slotV (v : V) (i : ZMod (2 * j + 1)) :
    (X inc j τ σ R slotV slotU NS).Adj (.inr (.inl v)) (.inl (slotV v i, i)) :=
  (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl rfl⟩

theorem RHyp.adj_slotU (u : U) (i : ZMod (2 * j + 1)) :
    (X inc j τ σ R slotV slotU NS).Adj (.inr (.inr u)) (.inl (slotU u i, i)) :=
  (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl rfl⟩

theorem RHyp.hubs (a b : V ⊕ U) : Reach (X inc j τ σ R slotV slotU NS) (.inr a) (.inr b) 7 := by
  rcases a with v | u <;> rcases b with v' | u'
  · rcases H.r3V v v' with ⟨i, h⟩ | h
    · have h1 := Reach.adj (H.adj_slotV v i)
      have h2 := h.map (lvl inc j τ σ R slotV slotU NS i)
      have h3 := (Reach.adj (H.adj_slotV v' i)).symm
      exact ((h1.trans h2).trans h3).mono (by norm_num)
    · exact (h.map (hubHom inc j τ σ R slotV slotU NS)).mono (by norm_num)
  · have h1 := Reach.adj (H.adj_slotV v 0)
    have h2 := (H.base.odd (x := slotV v 0) (y := slotU u' 0) (by rw [H.slotA, H.slotB]; simp)).map
      (lvl inc j τ σ R slotV slotU NS 0)
    have h3 := (Reach.adj (H.adj_slotU u' 0)).symm
    exact (h1.trans h2).trans h3
  · have h1 := Reach.adj (H.adj_slotU u 0)
    have h2 := (H.base.odd (x := slotU u 0) (y := slotV v' 0) (by rw [H.slotA, H.slotB]; simp)).map
      (lvl inc j τ σ R slotV slotU NS 0)
    have h3 := (Reach.adj (H.adj_slotV v' 0)).symm
    exact (h1.trans h2).trans h3
  · rcases H.r3U u u' with ⟨i, h⟩ | h
    · have h1 := Reach.adj (H.adj_slotU u i)
      have h2 := h.map (lvl inc j τ σ R slotV slotU NS i)
      have h3 := (Reach.adj (H.adj_slotU u' i)).symm
      exact ((h1.trans h2).trans h3).mono (by norm_num)
    · exact (h.map (hubHom inc j τ σ R slotV slotU NS)).mono (by norm_num)

theorem RHyp.reach7 (a b : Typed.Vtx P L V U j) : Reach (X inc j τ σ R slotV slotU NS) a b 7 := by
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
theorem RHyp.ediam_le : (X inc j τ σ R slotV slotU NS).ediam ≤ 7 :=
  SimpleGraph.ediam_le_iff.2 fun a b => (H.reach7 a b).edist_le

end Dist

/-! ## Colouring, degrees, order (as in `Typed`) -/

section Degree

variable (H : RHyp inc j τ σ R slotV slotU NS)
include H

theorem RHyp.rel_col {a b : Typed.Vtx P L V U j} (h : rel inc j τ σ R slotV slotU NS a b) : col τ a ≠ col τ b := by
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

theorem RHyp.colorable : (X inc j τ σ R slotV slotU NS).Colorable 2 :=
  ⟨Coloring.mk (col τ) fun {a b} h => by
    rcases (SimpleGraph.fromRel_adj _ _ _).1 h with ⟨-, h' | h'⟩
    · exact H.rel_col h'
    · exact (H.rel_col h').symm⟩

variable [Fintype P] [Fintype L] [Fintype V] [Fintype U] {q : ℕ}

theorem RHyp.deg_A (hdeg : ∀ x : P ⊕ L, (univ.filter ((Hexagon.incGraph inc).Adj x)).card ≤ q + 1)
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

theorem RHyp.deg_B (hdeg : ∀ x : P ⊕ L, (univ.filter ((Hexagon.incGraph inc).Adj x)).card ≤ q + 1)
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

theorem RHyp.deg_hubV (hNV : ∀ v, (univ.filter (NS v)).card ≤ q - j) (hjq : j ≤ q) (v : V) :
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

theorem RHyp.deg_hubU (hNU : ∀ u, (univ.filter (fun v => NS v u)).card ≤ q - j) (hjq : j ≤ q) (u : U) :
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
theorem RHyp.exists_graph (hdeg : ∀ x : P ⊕ L, (univ.filter ((Hexagon.incGraph inc).Adj x)).card ≤ q + 1)
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

end BipartiteDD.LeanAll.Route
