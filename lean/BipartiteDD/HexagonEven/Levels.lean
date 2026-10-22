import BipartiteDD.HexagonEven.Spread
import BipartiteDD.HexagonD.Forest

/-! Theorem D, slice 2, part 6 (targets 2 and 3): Delorme's levels on `H(q)`, with whiskers.

Notation: `V = SPt F ⊕ HLine F` is the vertex set of the incidence graph `G` of `H(q)`; `d` is such that `-d` is
a non-square, `v ∈ S` a line of the spread, `W` a set of *whiskers*: lines opposite `v`, not in `S`, with no
*free* point (a point off `Π` on no line meeting `v`, i.e. at distance `5` from `v`) on two of them.
`W = ∅` gives Delorme's levels (target 2).

* `A2 = {v}`;
* `A1 = {v} ∪ points(v) ∪ S`;
* `A0 = A1 ∪ {lines meeting v} ∪ {singular points of Π} ∪ W`.

This file proves hypotheses (a), (b) of `delorme_levelled_polygon` and `ForestDiam G A0 4`. -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonEven

open BipartiteDD.HexagonD

open BipartiteDD.Hexagon BipartiteDD.Doubling Module Submodule

/-- A set of a sum type from two sets. -/
def sumSet {α β : Type*} (X : Set α) (Y : Set β) : Set (α ⊕ β) := Sum.inl '' X ∪ Sum.inr '' Y

@[simp] theorem inl_mem_sumSet {α β : Type*} {X : Set α} {Y : Set β} {a : α} :
    Sum.inl a ∈ sumSet X Y ↔ a ∈ X := by simp [sumSet]

@[simp] theorem inr_mem_sumSet {α β : Type*} {X : Set α} {Y : Set β} {b : β} :
    Sum.inr b ∈ sumSet X Y ↔ b ∈ Y := by simp [sumSet]

theorem ncard_sumSet {α β : Type*} (X : Set α) (Y : Set β) [Finite α] [Finite β] :
    (sumSet X Y).ncard = X.ncard + Y.ncard := by
  unfold sumSet
  rw [Set.ncard_union_eq, Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_image_of_injective _ Sum.inr_injective]
  · rw [Set.disjoint_left]
    rintro _ ⟨a, -, rfl⟩ ⟨b, -, h⟩
    exact Sum.inr_ne_inl h

variable {F : Type*} [Field F] [Fintype F] {d : F}

/-- The point lies in `Π`. -/
def OnPiE (d : F) (p : SPt F) : Prop := p.1.rep 0 + p.1.rep 3 + d * p.1.rep 4 = 0

/-- The line `l` meets the line `v`. -/
def Meets (v l : HLine F) : Prop := ∃ r : SPt F, hexInc r v ∧ hexInc r l

/-- Whiskers for the spread line `v`. -/
structure Whiskers (d : F) (v : SLineE d) (W : Set (HLine F)) : Prop where
  not_inPi : ∀ w ∈ W, ¬ InPiE d w
  opp : ∀ w ∈ W, Opp (hexInc (F := F)) v.1 w
  free : ∀ p : SPt F, ¬ OnPiE d p → (¬ ∃ M, hexInc p M ∧ Meets v.1 M) →
    ∀ w ∈ W, ∀ w' ∈ W, hexInc p w → hexInc p w' → w = w'

/-- The doubled set `A₀` of Delorme's levels (with whiskers `W`). -/
def A0 (d : F) (v : HLine F) (W : Set (HLine F)) : Set (SPt F ⊕ HLine F) :=
  sumSet {p | OnPiE d p} {l | InPiE d l ∨ Meets v l ∨ l ∈ W}

/-- `A₁ = {v} ∪ points(v) ∪ S`. -/
def A1 (d : F) (v : HLine F) : Set (SPt F ⊕ HLine F) :=
  sumSet {p | hexInc p v} {l | InPiE d l}

/-- `A₂ = {v}`. -/
def A2 (v : HLine F) : Set (SPt F ⊕ HLine F) := {Sum.inr v}

/-- The levels as a decreasing sequence of sets. -/
def lev (d : F) (v : HLine F) (W : Set (HLine F)) : ℕ → Set (SPt F ⊕ HLine F)
  | 0 => A0 d v W
  | 1 => A1 d v
  | 2 => A2 v
  | _ + 3 => ∅

local notation "GH" => Hexagon.incGraph (hexInc (F := F))

theorem onPi_of_mem {s : SLineE d} {p : SPt F} (h : hexInc p s.1) : OnPiE d p := s.2 _ h

section Lemmas

/-- Two distinct points of `Π` on a line put the line inside `Π`. -/
theorem inPi_of_two_points {l : HLine F} {p p' : SPt F} (hp : OnPiE d p) (hp' : OnPiE d p')
    (h1 : hexInc p l) (h2 : hexInc p' l) (hne : p ≠ p') : InPiE d l := by
  have hMspan : l.1 = span F {p.1.rep, p'.1.rep} :=
    hline_eq_span l h1 h2 p.1.rep_nonzero (rep_not_mem_span_of_ne (fun h => hne (Subtype.ext h)))
  intro x hx
  rw [hMspan] at hx
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hp : p.1.rep 0 + p.1.rep 3 + d * p.1.rep 4 = 0 := hp
  have hp' : p'.1.rep 0 + p'.1.rep 3 + d * p'.1.rep 4 = 0 := hp'
  linear_combination a * hp + b * hp'

theorem eq_of_onPi_of_not_inPi {l : HLine F} {p p' : SPt F} (hp : OnPiE d p) (hp' : OnPiE d p')
    (h1 : hexInc p l) (h2 : hexInc p' l) (hl : ¬ InPiE d l) : p = p' := by
  by_contra hne
  exact hl (inPi_of_two_points hp hp' h1 h2 hne)

theorem eq_of_inPi_of_mem (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (hchar : (2 : F) = 0) {l l' : HLine F} {p : SPt F} (hl : InPiE d l) (hl' : InPiE d l')
    (hp : hexInc p l) (hp' : hexInc p l') : l = l' := by
  have := slineE_unique hd hchar p.1.rep_nonzero p.2 (onPi_of_mem (s := ⟨l, hl⟩) hp) (s := ⟨l, hl⟩)
    (s' := ⟨l', hl'⟩) hp hp'
  exact congrArg Subtype.val this

end Lemmas

end BipartiteDD.HexagonEven
