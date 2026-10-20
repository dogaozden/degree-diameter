import BipartiteDD.HexagonD.RegHex

/-! Theorem D, slice 2, part 24 (target 5): canonical neighbours, degree lower bounds, twins.

`α = VerL`, `β = VerR` are the versions of points and lines, `r = rel hexInc m hgt`. The pool
`isP b` of deletable line versions: the version of a line of the spread whose last letter is nonzero.
* a deleted version `b ∈ P` has a surviving twin with last letter `0` (`htwin_P`);
* every version, after deleting any `S ⊆ P`, keeps at least `q + 1` neighbours (`deg_ge`): for each of the `q + 1`
  neighbours `y` of the underlying vertex take the version of `y` obtained by padding with `0`; such a version
  of a spread line has last letter `0`, so it is not in `P`. -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon BipartiteDD.Doubling BipartiteDD.Regular
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)] {c : F} {c0 c1 : F} {m : ℕ}

/-- Versions of points / lines in the exact levelled hexagon. -/
abbrev VL (c c0 c1 : F) (m : ℕ) := VerL (SPt F) (HLine F) m (hgt c c0 c1)
abbrev VR (c c0 c1 : F) (m : ℕ) := VerR (SPt F) (HLine F) m (hgt c c0 c1)

/-- The incidence relation of versions. -/
abbrev rr (c c0 c1 : F) (m : ℕ) : VL c c0 c1 m → VR c c0 c1 m → Prop := rel hexInc m (hgt c c0 c1)

/-- The canonical version of the line `l` above the point version `a`: pad with `0`. -/
noncomputable def canR (hm : 0 < m) (a : VL c c0 c1 m) (l : HLine F) : VR c c0 c1 m :=
  ⟨l, extStr (Sum.inl a.1) a.2 ⟨0, hm⟩ (Sum.inr l)⟩

/-- The canonical version of the point `p` below the line version `b`. -/
noncomputable def canL (hm : 0 < m) (b : VR c c0 c1 m) (p : SPt F) : VL c c0 c1 m :=
  ⟨p, extStr (Sum.inr b.1) b.2 ⟨0, hm⟩ (Sum.inl p)⟩

theorem agree_extStr {V : Type*} {h : V → ℕ} {m : ℕ} (u : V) (s : Fin (h u) → Fin m) (c : Fin m) (v : V) :
    Agree s (extStr u s c v) := fun i ha hb => by simp [extStr, ha]

theorem rr_canR (hm : 0 < m) (a : VL c c0 c1 m) {l : HLine F} (hl : hexInc a.1 l) :
    rr c c0 c1 m a (canR hm a l) := ⟨hl, agree_extStr _ _ _ _⟩

theorem rr_canL (hm : 0 < m) (b : VR c c0 c1 m) {p : SPt F} (hp : hexInc p b.1) :
    rr c c0 c1 m (canL hm b p) b := ⟨hp, (agree_extStr (h := hgt c c0 c1) (Sum.inr b.1) b.2 ⟨0, hm⟩
      (Sum.inl p)).symm⟩

/-- The pool of deletable line versions: a line of the spread with a nonzero last letter. -/
def isP (c c0 c1 : F) {m : ℕ} (hm : 0 < m) (b : VR c c0 c1 m) : Prop :=
  InPi c b.1 ∧ ∃ i : Fin (hgt c c0 c1 (Sum.inr b.1)), i.1 + 1 = hgt c c0 c1 (Sum.inr b.1) ∧
    b.2 i ≠ ⟨0, hm⟩

/-- Padding with `0` over a point of a spread line gives a version outside the pool. -/
theorem canR_not_isP (hc : ¬ IsSquare (-c)) (hm : 0 < m) (a : VL c c0 c1 m) {l : HLine F}
    (hl : hexInc a.1 l) : ¬ isP c c0 c1 hm (canR hm a l) := by
  rintro ⟨hlPi, i, hi, hne⟩
  have h1 := hgt_pt_on_sline (c0 := c0) (c1 := c1) hc hlPi hl
  have hi' : (i : ℕ) + 1 = hgt c c0 c1 (Sum.inr l) := hi
  apply hne
  show extStr (Sum.inl a.1) a.2 ⟨0, hm⟩ (Sum.inr l) i = ⟨0, hm⟩
  have hnot : ¬ ((i : ℕ) < hgt c c0 c1 (Sum.inl a.1)) := by omega
  unfold extStr
  rw [dite_cond_eq_false (eq_false hnot)]

end BipartiteDD.HexagonD
