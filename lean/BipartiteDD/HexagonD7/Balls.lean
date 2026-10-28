import BipartiteDD.HexagonD7.Main

/-! Diameter 7 from a generalized hexagon, part 6: closed 2-balls.

`ballP r` = `r` and the points collinear with it, `ballL l` = `l` and the lines concurrent with it. With no digons
(two points on two common lines force the lines equal) and `q + 1` lines per point and points per line, both have
`1 + (q + 1) q` elements. -/

namespace BipartiteDD.HexagonD7

open Finset
open scoped Classical

variable {P L : Type*} [Fintype P] [Fintype L] {inc : P → L → Prop}

/-- `r` together with the points collinear with `r`. -/
noncomputable def ballP (inc : P → L → Prop) (r : P) : Finset P := univ.filter (fun z => z = r ∨ Coll inc r z)

/-- `l` together with the lines concurrent with `l`. -/
noncomputable def ballL (inc : P → L → Prop) (l : L) : Finset L := univ.filter (fun m => m = l ∨ Conc inc l m)

theorem mem_ballP {r z : P} : z ∈ ballP inc r ↔ z = r ∨ Coll inc r z := by simp [ballP]

theorem mem_ballL {l m : L} : m ∈ ballL inc l ↔ m = l ∨ Conc inc l m := by simp [ballL]

theorem self_mem_ballP (r : P) : r ∈ ballP inc r := mem_ballP.2 (Or.inl rfl)

theorem self_mem_ballL (l : L) : l ∈ ballL inc l := mem_ballL.2 (Or.inl rfl)

theorem Coll.symm {r p : P} (h : Coll inc r p) : Coll inc p r := by
  obtain ⟨hne, l, h1, h2⟩ := h; exact ⟨Ne.symm hne, l, h2, h1⟩

theorem Conc.symm {l m : L} (h : Conc inc l m) : Conc inc m l := by
  obtain ⟨hne, p, h1, h2⟩ := h; exact ⟨Ne.symm hne, p, h2, h1⟩

theorem mem_ballP_comm {r z : P} : z ∈ ballP inc r ↔ r ∈ ballP inc z := by
  simp only [mem_ballP]
  constructor
  · rintro (rfl | h) <;> [exact Or.inl rfl; exact Or.inr h.symm]
  · rintro (rfl | h) <;> [exact Or.inl rfl; exact Or.inr h.symm]

theorem mem_ballL_comm {l m : L} : m ∈ ballL inc l ↔ l ∈ ballL inc m := by
  simp only [mem_ballL]
  constructor
  · rintro (rfl | h) <;> [exact Or.inl rfl; exact Or.inr h.symm]
  · rintro (rfl | h) <;> [exact Or.inl rfl; exact Or.inr h.symm]

section Count

variable {q : ℕ}
  (hdig : ∀ {p r : P} {M₁ M₂ : L}, p ≠ r → inc p M₁ → inc r M₁ → inc p M₂ → inc r M₂ → M₁ = M₂)
  (hP : ∀ p, (univ.filter (inc p)).card = q + 1) (hL : ∀ l, (univ.filter (fun p => inc p l)).card = q + 1)
include hdig hP hL

theorem card_ballP (r : P) : (ballP inc r).card = 1 + (q + 1) * q := by
  set T := (univ.filter (inc r)).biUnion (fun l => (univ.filter (fun p => inc p l)).erase r) with hT
  have hrT : r ∉ T := by simp [hT]
  have heq : ballP inc r = insert r T := by
    ext z
    simp only [mem_ballP, Coll, mem_insert, hT, mem_biUnion, mem_filter, mem_univ, true_and, mem_erase]
    constructor
    · rintro (rfl | ⟨hne, l, hr, hz⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨l, hr, Ne.symm hne, hz⟩
    · rintro (rfl | ⟨l, hr, hne, hz⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨Ne.symm hne, l, hr, hz⟩
  have hdisj : ∀ l ∈ univ.filter (inc r), ∀ l' ∈ univ.filter (inc r), l ≠ l' →
      Disjoint ((univ.filter (fun p => inc p l)).erase r) ((univ.filter (fun p => inc p l')).erase r) := by
    intro l hl l' hl' hne
    rw [Finset.disjoint_left]
    intro z hz hz'
    simp only [mem_erase, mem_filter, mem_univ, true_and] at hz hz' hl hl'
    exact hne (hdig hz.1 hz.2 hl hz'.2 hl')
  have hTcard : T.card = (q + 1) * q := by
    rw [hT, card_biUnion hdisj]
    have : ∀ l ∈ univ.filter (inc r), ((univ.filter (fun p => inc p l)).erase r).card = q := by
      intro l hl
      simp only [mem_filter, mem_univ, true_and] at hl
      rw [card_erase_of_mem (by simpa using hl), hL l]; rfl
    rw [sum_congr rfl this, sum_const, hP r, smul_eq_mul]
  rw [heq, card_insert_of_notMem hrT, hTcard]; ring

theorem card_ballL (l : L) : (ballL inc l).card = 1 + (q + 1) * q := by
  set T := (univ.filter (fun p => inc p l)).biUnion (fun x => (univ.filter (inc x)).erase l) with hT
  have hlT : l ∉ T := by simp [hT]
  have heq : ballL inc l = insert l T := by
    ext m
    simp only [mem_ballL, Conc, mem_insert, hT, mem_biUnion, mem_filter, mem_univ, true_and, mem_erase]
    constructor
    · rintro (rfl | ⟨hne, x, hl, hm⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨x, hl, Ne.symm hne, hm⟩
    · rintro (rfl | ⟨x, hl, hne, hm⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨Ne.symm hne, x, hl, hm⟩
  have hdisj : ∀ x ∈ univ.filter (fun p => inc p l), ∀ y ∈ univ.filter (fun p => inc p l), x ≠ y →
      Disjoint ((univ.filter (inc x)).erase l) ((univ.filter (inc y)).erase l) := by
    intro x hx y hy hne
    rw [Finset.disjoint_left]
    intro m hm hm'
    simp only [mem_erase, mem_filter, mem_univ, true_and] at hm hm' hx hy
    exact hm.1 (hdig hne hm.2 hm'.2 hx hy)
  have hTcard : T.card = (q + 1) * q := by
    rw [hT, card_biUnion hdisj]
    have : ∀ x ∈ univ.filter (fun p => inc p l), ((univ.filter (inc x)).erase l).card = q := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      rw [card_erase_of_mem (by simpa using hx), hP x]; rfl
    rw [sum_congr rfl this, sum_const, hL l, smul_eq_mul]
  rw [heq, card_insert_of_notMem hlT, hTcard]; ring

end Count

end BipartiteDD.HexagonD7
