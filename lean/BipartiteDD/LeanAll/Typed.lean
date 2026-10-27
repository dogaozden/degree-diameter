import BipartiteDD.HexagonD7.Main

/-! # Typed levels over a generalized hexagon (research/squads/cells/d16D7.md)

`2j + 1` levels `i`, each a copy of the incidence graph `I` of an incidence structure `(P, L, inc)` (vertices
`P ⊕ L`), with a type `τ i`: the class `A_i` is the points (`τ i = false`) or the lines (`τ i = true`), `B_i` the
other class. For every level `i` and `1 ≤ k ≤ j` a bijection `σ i k` of `P ⊕ L` maps `A_i` onto `B_{i+k}`, and the
edges `(x, i) ~ (σ i k x, i + k)`, `x ∈ A_i`, are present except for `x` in a freed set `R i k ⊆ A_i`. Line-side hubs
`v : V` take one `A`-vertex `slotV v i` in every level, point-side hubs `u : U` one `B`-vertex `slotU u i`, and a hub
graph `NS` joins hubs of the two kinds.

`THyp`: every point is joined to every line within `5` in `I`, every element has two neighbours (as in
`HexagonD7.Hyp`); at every transition the freed set is co-adjacency free (H1) and `σ` maps the elements co-adjacent
to a freed `r` onto those co-adjacent to `σ r` (H3); two hubs of the same kind are within `4` through their slots in
some level or within `6` in the hub graph. Then `X` has diameter at most `7` (`THyp.ediam_le`); `exists_graph` adds
the colouring, the degree bound `q + 1 + j` (each slot taken by at most as many hubs as edges were freed there) and
the order `(2j + 1)(|P| + |L|) + |V| + |U|`. The proof of the distance bound is the one of `HexagonD7.Hyp.cross`
with colour-generic covering lemmas; hubs are not needed between level vertices. -/

namespace BipartiteDD.LeanAll.Typed

open SimpleGraph Finset BipartiteDD.Hexagon BipartiteDD.HexagonD7
open scoped Classical

set_option linter.unusedSectionVars false

variable {P L V U : Type*}

/-- The class of an element: `false` for points, `true` for lines. -/
def colE : P ⊕ L → Bool
  | .inl _ => false
  | .inr _ => true

/-- Two different elements with a common neighbour. -/
def Co (inc : P → L → Prop) (x y : P ⊕ L) : Prop := x ≠ y ∧ ∃ z, (Hexagon.incGraph inc).Adj x z ∧ (Hexagon.incGraph inc).Adj z y

section Defs

variable (inc : P → L → Prop) (j : ℕ) (τ : ZMod (2 * j + 1) → Bool)
  (σ : ZMod (2 * j + 1) → ℕ → (P ⊕ L) ≃ (P ⊕ L)) (R : ZMod (2 * j + 1) → ℕ → Set (P ⊕ L))
  (slotV : V → ZMod (2 * j + 1) → P ⊕ L) (slotU : U → ZMod (2 * j + 1) → P ⊕ L) (NS : V → U → Prop)

/-- Vertices: level vertices and hubs. -/
abbrev Vtx (P L V U : Type*) (j : ℕ) := ((P ⊕ L) × ZMod (2 * j + 1)) ⊕ (V ⊕ U)

/-- The directed edge relation. -/
def rel : Vtx P L V U j → Vtx P L V U j → Prop
  | .inl (x, i), .inl (y, i') => ((Hexagon.incGraph inc).Adj x y ∧ i = i') ∨
      (∃ k : ℕ, 1 ≤ k ∧ k ≤ j ∧ i' = i + k ∧ colE x = τ i ∧ x ∉ R i k ∧ y = σ i k x)
  | .inr (.inl v), .inl (x, i) => x = slotV v i
  | .inr (.inr u), .inl (x, i) => x = slotU u i
  | .inr (.inl v), .inr (.inr u) => NS v u
  | _, _ => False

/-- The graph. -/
def X : SimpleGraph (Vtx P L V U j) := SimpleGraph.fromRel (rel inc j τ σ R slotV slotU NS)

/-- Level `i`. -/
def lvl (i : ZMod (2 * j + 1)) : Hexagon.incGraph inc →g X inc j τ σ R slotV slotU NS where
  toFun x := .inl (x, i)
  map_rel' := fun h => (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp [h.ne], Or.inl (Or.inl ⟨h, rfl⟩)⟩

/-- The hub graph inside `X`. -/
def hubHom : hubGraph NS →g X inc j τ σ R slotV slotU NS where
  toFun x := .inr x
  map_rel' := by
    intro a b h
    rcases (SimpleGraph.fromRel_adj _ _ _).1 h with ⟨hne, h' | h'⟩
    · rcases a with v | u <;> rcases b with v' | u'
      · exact absurd h' id
      · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl h'⟩
      · exact absurd h' id
      · exact absurd h' id
    · rcases a with v | u <;> rcases b with v' | u'
      · exact absurd h' id
      · exact absurd h' id
      · exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inr h'⟩
      · exact absurd h' id

end Defs

/-! ## The incidence graph -/

section Inc

variable {inc : P → L → Prop}

theorem colE_adj {x y : P ⊕ L} (h : (Hexagon.incGraph inc).Adj x y) : colE x ≠ colE y := by
  rcases x with p | l <;> rcases y with p' | l'
  · exact absurd h Hexagon.incGraph_not_adj_inl_inl
  · simp [colE]
  · simp [colE]
  · exact absurd h Hexagon.incGraph_not_adj_inr_inr

theorem Co.colE_eq {x y : P ⊕ L} (h : Co inc x y) : colE x = colE y := by
  obtain ⟨-, z, h1, h2⟩ := h
  have := colE_adj h1; have := colE_adj h2
  cases hx : colE x <;> cases hz : colE z <;> cases hy : colE y <;> simp_all

theorem Co.reach {x y : P ⊕ L} (h : Co inc x y) : Reach (Hexagon.incGraph inc) x y 2 := by
  obtain ⟨-, z, h1, h2⟩ := h
  exact (Reach.adj h1).trans (Reach.adj h2)

theorem Co.symm {x y : P ⊕ L} (h : Co inc x y) : Co inc y x := by
  obtain ⟨hne, z, h1, h2⟩ := h
  exact ⟨hne.symm, z, h2.symm, h1.symm⟩

/-- The base facts of `HexagonD7.Hyp`. -/
structure Base (inc : P → L → Prop) : Prop where
  pl : ∀ p l, Reach (Hexagon.incGraph inc) (.inl p) (.inr l) 5
  p2 : ∀ p, ∃ l l', l ≠ l' ∧ inc p l ∧ inc p l'
  l2 : ∀ l, ∃ p p', p ≠ p' ∧ inc p l ∧ inc p' l

theorem Base.odd (hB : Base inc) {x y : P ⊕ L} (h : colE x ≠ colE y) : Reach (Hexagon.incGraph inc) x y 5 := by
  rcases x with p | l <;> rcases y with p' | l'
  · simp [colE] at h
  · exact hB.pl p l'
  · exact (hB.pl p' l).symm
  · simp [colE] at h

/-- Every element has two different neighbours. -/
theorem Base.two (hB : Base inc) (x : P ⊕ L) :
    ∃ y y', y ≠ y' ∧ (Hexagon.incGraph inc).Adj x y ∧ (Hexagon.incGraph inc).Adj x y' := by
  rcases x with p | l
  · obtain ⟨l, l', hne, hl, hl'⟩ := hB.p2 p
    exact ⟨.inr l, .inr l', by simpa using hne, Hexagon.incGraph_adj_inl_inr.2 hl, Hexagon.incGraph_adj_inl_inr.2 hl'⟩
  · obtain ⟨p, p', hne, hp, hp'⟩ := hB.l2 l
    exact ⟨.inl p, .inl p', by simpa using hne, Hexagon.incGraph_adj_inr_inl.2 hp, Hexagon.incGraph_adj_inr_inl.2 hp'⟩

theorem Base.all6 (hB : Base inc) (x y : P ⊕ L) : Reach (Hexagon.incGraph inc) x y 6 := by
  by_cases h : colE x = colE y
  · obtain ⟨z, -, -, hz, -⟩ := hB.two y
    have hc : colE x ≠ colE z := by rw [h]; exact colE_adj hz
    exact (hB.odd hc).trans (Reach.adj hz.symm)
  · exact (hB.odd h).mono (by norm_num)

/-- **Covering lemma**, for either class. -/
theorem Base.coverE (hB : Base inc) {u x : P ⊕ L} (h : colE u ≠ colE x) :
    ∃ u', Co inc u u' ∧ Reach (Hexagon.incGraph inc) u' x 3 := by
  rcases u with p | l <;> rcases x with p' | l'
  · simp [colE] at h
  · obtain ⟨q, ⟨hne, m, h1, h2⟩, hr⟩ := HexagonD7.cover_dual hB.l2 (hB.pl p l')
    exact ⟨.inl q, ⟨by simpa using hne, .inr m, Hexagon.incGraph_adj_inl_inr.2 h1, Hexagon.incGraph_adj_inr_inl.2 h2⟩, hr⟩
  · obtain ⟨m, ⟨hne, q, h1, h2⟩, hr⟩ := HexagonD7.cover hB.p2 (hB.pl p' l).symm
    exact ⟨.inr m, ⟨by simpa using hne, .inl q, Hexagon.incGraph_adj_inr_inl.2 h1, Hexagon.incGraph_adj_inl_inr.2 h2⟩, hr⟩
  · simp [colE] at h

end Inc

/-! ## Theorem -/

variable {inc : P → L → Prop} {j : ℕ} {τ : ZMod (2 * j + 1) → Bool}
  {σ : ZMod (2 * j + 1) → ℕ → (P ⊕ L) ≃ (P ⊕ L)} {R : ZMod (2 * j + 1) → ℕ → Set (P ⊕ L)}
  {slotV : V → ZMod (2 * j + 1) → P ⊕ L} {slotU : U → ZMod (2 * j + 1) → P ⊕ L} {NS : V → U → Prop}

/-- The hypotheses. -/
structure THyp (inc : P → L → Prop) (j : ℕ) (τ : ZMod (2 * j + 1) → Bool)
    (σ : ZMod (2 * j + 1) → ℕ → (P ⊕ L) ≃ (P ⊕ L)) (R : ZMod (2 * j + 1) → ℕ → Set (P ⊕ L))
    (slotV : V → ZMod (2 * j + 1) → P ⊕ L) (slotU : U → ZMod (2 * j + 1) → P ⊕ L) (NS : V → U → Prop) : Prop where
  base : Base inc
  maps : ∀ i (k : ℕ), 1 ≤ k → k ≤ j → ∀ x, colE x = τ i → colE (σ i k x) = !τ (i + k)
  onto : ∀ i (k : ℕ), 1 ≤ k → k ≤ j → ∀ y, colE y = !τ (i + k) → colE ((σ i k).symm y) = τ i
  rA : ∀ i (k : ℕ), 1 ≤ k → k ≤ j → ∀ x ∈ R i k, colE x = τ i
  r1 : ∀ i (k : ℕ), 1 ≤ k → k ≤ j → ∀ r ∈ R i k, ∀ s ∈ R i k, ¬ Co inc r s
  r2 : ∀ i (k : ℕ), 1 ≤ k → k ≤ j → ∀ r ∈ R i k, ∀ x, Co inc r x ↔ Co inc (σ i k r) (σ i k x)
  slotA : ∀ v i, colE (slotV v i) = τ i
  slotB : ∀ u i, colE (slotU u i) = !τ i
  r3V : ∀ v v', (∃ i, Reach (Hexagon.incGraph inc) (slotV v i) (slotV v' i) 4) ∨ Reach (hubGraph NS) (.inl v) (.inl v') 6
  r3U : ∀ u u', (∃ i, Reach (Hexagon.incGraph inc) (slotU u i) (slotU u' i) 4) ∨ Reach (hubGraph NS) (.inr u) (.inr u') 6

theorem shift_ne (i : ZMod (2 * j + 1)) {k : ℕ} (hk1 : 1 ≤ k) (hkj : k ≤ j) : i + k ≠ i := by
  intro h
  have h0 : ((k : ℕ) : ZMod (2 * j + 1)) = 0 := by
    have := congrArg (· - i) h; simpa using this
  have := congrArg ZMod.val h0
  rw [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt (by omega)] at this
  omega

section Dist

variable (H : THyp inc j τ σ R slotV slotU NS)
include H

theorem THyp.adj_shift {x : P ⊕ L} {i : ZMod (2 * j + 1)} {k : ℕ} (hk1 : 1 ≤ k) (hkj : k ≤ j) (hx : colE x = τ i)
    (hR : x ∉ R i k) : (X inc j τ σ R slotV slotU NS).Adj (.inl (x, i)) (.inl (σ i k x, i + k)) :=
  (SimpleGraph.fromRel_adj _ _ _).2 ⟨fun h => shift_ne i hk1 hkj (congrArg Prod.snd (Sum.inl_injective h)).symm,
    Or.inl (Or.inr ⟨k, hk1, hkj, rfl, hx, hR, rfl⟩)⟩

theorem THyp.level (x y : P ⊕ L) (i : ZMod (2 * j + 1)) :
    Reach (X inc j τ σ R slotV slotU NS) (.inl (x, i)) (.inl (y, i)) 6 :=
  (H.base.all6 x y).map (lvl inc j τ σ R slotV slotU NS i)

/-- A freed element reaches every `A`-element of the target level within `6`. -/
theorem THyp.freed {r b : P ⊕ L} {i : ZMod (2 * j + 1)} {k : ℕ} (hk1 : 1 ≤ k) (hkj : k ≤ j) (hr : r ∈ R i k)
    (hb : colE b = τ (i + k)) :
    Reach (X inc j τ σ R slotV slotU NS) (.inl (r, i)) (.inl (b, i + k)) 6 := by
  have hrA := H.rA i k hk1 hkj r hr
  have hσr := H.maps i k hk1 hkj r hrA
  obtain ⟨u', hco, hreach⟩ := H.base.coverE (u := σ i k r) (x := b) (by rw [hσr, hb]; simp)
  set p' := (σ i k).symm u' with hp'
  have hσp : σ i k p' = u' := by simp [hp']
  have hp'A : colE p' = τ i := H.onto i k hk1 hkj u' (by rw [← hco.colE_eq, hσr])
  have hco' : Co inc r p' := (H.r2 i k hk1 hkj r hr p').2 (by rw [hσp]; exact hco)
  have hp'R : p' ∉ R i k := fun h => H.r1 i k hk1 hkj r hr p' h hco'
  have h1 := hco'.reach.map (lvl inc j τ σ R slotV slotU NS i)
  have h2 := Reach.adj (H.adj_shift hk1 hkj hp'A hp'R)
  have h3 := hreach.map (lvl inc j τ σ R slotV slotU NS (i + k))
  rw [hσp] at h2
  exact ((h1.trans h2).trans h3).mono (by norm_num)

/-- Two vertices in levels `i` and `i + k`. -/
theorem THyp.cross (x y : P ⊕ L) (i : ZMod (2 * j + 1)) {k : ℕ} (hk1 : 1 ≤ k) (hkj : k ≤ j) :
    Reach (X inc j τ σ R slotV slotU NS) (.inl (x, i)) (.inl (y, i + k)) 7 := by
  by_cases hxA : colE x = τ i
  · by_cases hxR : x ∈ R i k
    · by_cases hyA : colE y = τ (i + k)
      · exact (H.freed hk1 hkj hxR hyA).mono (by norm_num)
      · obtain ⟨c, -, -, hc, -⟩ := H.base.two y
        have hcA : colE c = τ (i + k) := by
          have := colE_adj hc
          cases h1 : colE y <;> cases h2 : colE c <;> cases h3 : τ (i + k) <;> simp_all
        have h1 := H.freed hk1 hkj hxR hcA
        have h2 := (lvl inc j τ σ R slotV slotU NS (i + k)).map_rel hc.symm
        exact h1.trans (Reach.adj h2)
    · exact (Reach.adj (H.adj_shift hk1 hkj hxA hxR)).trans (H.level _ y _)
  · have hxB : colE x = !τ i := by cases h1 : colE x <;> cases h2 : τ i <;> simp_all
    by_cases hyA : colE y = τ (i + k)
    · -- some neighbour of `y` is not the image of a freed element
      obtain ⟨w, w', hne, hw, hw'⟩ := H.base.two y
      have hwB : ∀ z, (Hexagon.incGraph inc).Adj y z → colE z = !τ (i + k) := fun z hz => by
        have := colE_adj hz
        cases h1 : colE y <;> cases h2 : colE z <;> cases h3 : τ (i + k) <;> simp_all
      have hgood : ∃ z, (Hexagon.incGraph inc).Adj y z ∧ (σ i k).symm z ∉ R i k := by
        by_contra hcon
        push_neg at hcon
        have h1 := hcon w hw
        have h2 := hcon w' hw'
        have hco : Co inc (σ i k ((σ i k).symm w)) (σ i k ((σ i k).symm w')) := by
          simp only [Equiv.apply_symm_apply]; exact ⟨hne, y, hw.symm, hw'⟩
        exact H.r1 i k hk1 hkj _ h1 _ h2 ((H.r2 i k hk1 hkj _ h1 _).2 hco)
      obtain ⟨z, hz, hzR⟩ := hgood
      have hzA : colE ((σ i k).symm z) = τ i := H.onto i k hk1 hkj z (hwB z hz)
      have h1 := (H.base.odd (x := x) (y := (σ i k).symm z) (by rw [hxB, hzA]; simp)).map
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
      · obtain ⟨p', hco, hreach⟩ := H.base.coverE (u := r) (x := x) (by rw [hrA, hxB]; simp)
        have hp'R : p' ∉ R i k := fun h => H.r1 i k hk1 hkj r hrR p' h hco
        have hp'A : colE p' = τ i := by rw [← hco.colE_eq, hrA]
        have hco' := (H.r2 i k hk1 hkj r hrR p').1 hco
        rw [hσr] at hco'
        have h1 := hreach.symm.map (lvl inc j τ σ R slotV slotU NS i)
        have h2 := Reach.adj (H.adj_shift hk1 hkj hp'A hp'R)
        have h3 := hco'.reach.symm.map (lvl inc j τ σ R slotV slotU NS (i + k))
        exact ((h1.trans h2).trans h3).mono (by norm_num)
      · have h1 := (H.base.odd (x := x) (y := r) (by rw [hxB, hrA]; simp)).map
          (lvl inc j τ σ R slotV slotU NS i)
        have h2 := Reach.adj (H.adj_shift hk1 hkj hrA hrR)
        rw [hσr] at h2
        exact (h1.trans h2).mono (by norm_num)

theorem THyp.levels (x y : P ⊕ L) (i i' : ZMod (2 * j + 1)) :
    Reach (X inc j τ σ R slotV slotU NS) (.inl (x, i)) (.inl (y, i')) 7 := by
  by_cases h : i = i'
  · subst h; exact (H.level x y i).mono (by norm_num)
  · rcases shift_or h with ⟨k, hk1, hkj, rfl⟩ | ⟨k, hk1, hkj, rfl⟩
    · exact H.cross x y i hk1 hkj
    · exact (H.cross y x i' hk1 hkj).symm

theorem THyp.adj_slotV (v : V) (i : ZMod (2 * j + 1)) :
    (X inc j τ σ R slotV slotU NS).Adj (.inr (.inl v)) (.inl (slotV v i, i)) :=
  (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl rfl⟩

theorem THyp.adj_slotU (u : U) (i : ZMod (2 * j + 1)) :
    (X inc j τ σ R slotV slotU NS).Adj (.inr (.inr u)) (.inl (slotU u i, i)) :=
  (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl rfl⟩

theorem THyp.hubs (a b : V ⊕ U) : Reach (X inc j τ σ R slotV slotU NS) (.inr a) (.inr b) 7 := by
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

theorem THyp.reach7 (a b : Vtx P L V U j) : Reach (X inc j τ σ R slotV slotU NS) a b 7 := by
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
theorem THyp.ediam_le : (X inc j τ σ R slotV slotU NS).ediam ≤ 7 :=
  SimpleGraph.ediam_le_iff.2 fun a b => (H.reach7 a b).edist_le

end Dist

/-! ## Colouring, degrees, order -/

section Degree

/-- The colouring: `A`-vertices and point-side hubs `0`, `B`-vertices and line-side hubs `1`. -/
def col (τ : ZMod (2 * j + 1) → Bool) : Vtx P L V U j → Fin 2
  | .inl (x, i) => if colE x = τ i then 0 else 1
  | .inr (.inl _) => 1
  | .inr (.inr _) => 0

variable (H : THyp inc j τ σ R slotV slotU NS)
include H

theorem THyp.rel_col {a b : Vtx P L V U j} (h : rel inc j τ σ R slotV slotU NS a b) : col τ a ≠ col τ b := by
  rcases a with ⟨x, i⟩ | v | u <;> rcases b with ⟨y, i'⟩ | v' | u'
  · rcases h with ⟨hxy, rfl⟩ | ⟨k, hk1, hkj, rfl, hx, -, rfl⟩
    · have := colE_adj hxy
      simp only [col]
      cases h1 : colE x <;> cases h2 : colE y <;> cases h3 : τ i <;> simp_all
    · have := H.maps i k hk1 hkj x hx
      simp only [col, hx, this]
      cases τ (i + k) <;> simp
  · exact absurd h id
  · exact absurd h id
  · have h' : y = slotV v i' := h
    simp [col, h', H.slotA]
  · exact absurd h id
  · simp [col]
  · have h' : y = slotU u i' := h
    simp only [col, h', H.slotB]
    cases τ i' <;> simp
  · exact absurd h id
  · exact absurd h id

theorem THyp.colorable : (X inc j τ σ R slotV slotU NS).Colorable 2 :=
  ⟨Coloring.mk (col τ) fun {a b} h => by
    rcases (SimpleGraph.fromRel_adj _ _ _).1 h with ⟨-, h' | h'⟩
    · exact H.rel_col h'
    · exact (H.rel_col h').symm⟩

variable [Fintype P] [Fintype L] [Fintype V] [Fintype U] {q : ℕ}

theorem THyp.deg_A (hdeg : ∀ x : P ⊕ L, (univ.filter ((Hexagon.incGraph inc).Adj x)).card ≤ q + 1)
    (hSV : ∀ i x, (univ.filter (fun v => slotV v i = x)).card ≤ ((Finset.Icc 1 j).filter (fun k => x ∈ R i k)).card)
    {x : P ⊕ L} {i : ZMod (2 * j + 1)} (hxA : colE x = τ i) :
    ((X inc j τ σ R slotV slotU NS).neighborSet (.inl (x, i))).ncard ≤ q + 1 + j := by
  set A : Finset (Vtx P L V U j) := (univ.filter ((Hexagon.incGraph inc).Adj x)).image (fun y => .inl (y, i))
  set B : Finset (Vtx P L V U j) :=
    ((Finset.Icc 1 j).filter (fun k => x ∉ R i k)).image (fun k : ℕ => .inl (σ i k x, i + k))
  set C : Finset (Vtx P L V U j) := (univ.filter (fun v => slotV v i = x)).image (fun v => .inr (.inl v))
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

theorem THyp.deg_B (hdeg : ∀ x : P ⊕ L, (univ.filter ((Hexagon.incGraph inc).Adj x)).card ≤ q + 1)
    (hSU : ∀ i x, (univ.filter (fun u => slotU u i = x)).card ≤
      ((Finset.Icc 1 j).filter (fun k : ℕ => (σ (i - (k : ZMod (2 * j + 1))) k).symm x ∈ R (i - (k : ZMod (2 * j + 1))) k)).card)
    {x : P ⊕ L} {i : ZMod (2 * j + 1)} (hxB : colE x ≠ τ i) :
    ((X inc j τ σ R slotV slotU NS).neighborSet (.inl (x, i))).ncard ≤ q + 1 + j := by
  set A : Finset (Vtx P L V U j) := (univ.filter ((Hexagon.incGraph inc).Adj x)).image (fun y => .inl (y, i))
  set B : Finset (Vtx P L V U j) :=
    ((Finset.Icc 1 j).filter (fun k : ℕ => (σ (i - (k : ZMod (2 * j + 1))) k).symm x ∉ R (i - (k : ZMod (2 * j + 1))) k)).image
      (fun k : ℕ => .inl ((σ (i - (k : ZMod (2 * j + 1))) k).symm x, i - (k : ZMod (2 * j + 1))))
  set C : Finset (Vtx P L V U j) := (univ.filter (fun u => slotU u i = x)).image (fun u => .inr (.inr u))
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

theorem THyp.deg_hubV (hNV : ∀ v, (univ.filter (NS v)).card ≤ q - j) (hjq : j ≤ q) (v : V) :
    ((X inc j τ σ R slotV slotU NS).neighborSet (.inr (.inl v))).ncard ≤ q + 1 + j := by
  set A : Finset (Vtx P L V U j) := univ.image (fun i : ZMod (2 * j + 1) => .inl (slotV v i, i))
  set B : Finset (Vtx P L V U j) := (univ.filter (NS v)).image (fun u => .inr (.inr u))
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

theorem THyp.deg_hubU (hNU : ∀ u, (univ.filter (fun v => NS v u)).card ≤ q - j) (hjq : j ≤ q) (u : U) :
    ((X inc j τ σ R slotV slotU NS).neighborSet (.inr (.inr u))).ncard ≤ q + 1 + j := by
  set A : Finset (Vtx P L V U j) := univ.image (fun i : ZMod (2 * j + 1) => .inl (slotU u i, i))
  set B : Finset (Vtx P L V U j) := (univ.filter (fun v => NS v u)).image (fun v => .inr (.inl v))
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

/-- **The typed theorem.** A bipartite graph of maximum degree `q + 1 + j` and diameter at most `7` on
`(2j + 1)(|P| + |L|) + |V| + |U|` vertices. -/
theorem THyp.exists_graph (hdeg : ∀ x : P ⊕ L, (univ.filter ((Hexagon.incGraph inc).Adj x)).card ≤ q + 1)
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
  have hcard : Fintype.card (Vtx P L V U j) =
      (2 * j + 1) * (Fintype.card P + Fintype.card L) + Fintype.card V + Fintype.card U := by
    simp only [Vtx, Fintype.card_sum, Fintype.card_prod, ZMod.card]; ring
  exact ⟨_, isBipartiteDegDiam_comap (Fintype.equivFinOfCardEq hcard) hX⟩

end Degree

end BipartiteDD.LeanAll.Typed
