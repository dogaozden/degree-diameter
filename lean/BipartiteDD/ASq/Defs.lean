import Mathlib

/-! ASq, part 1: the Ahrens-Szekeres quadrangle AS(q) as an incidence structure.

Points are the triples `(a, (b, c))` of `F × F × F`, written `(a, w)` with `w = (b, c)`. The group law
is `(a, w)(a', w') = (a + a' + det w w', w + w')` with `det (b, c) (b', c') = b c' - c b'`.

Lines are the sets below. For `g ∈ F × F × F` and a direction `d ≠ 0` the coset `g Z_d`, where
`Z_d = {(0, t d)}`, is `lineA g d`. The fibres `fib w = {(μ, w) : μ ∈ F}` are the cosets of the centre.
A `Line F` is a set of this form. Everything here is a plain set-level statement, so distinct
parameters may give the same line; the counting lemmas in `ASq/Lines.lean` account for that. -/

namespace BipartiteDD.ASq

variable {F : Type*} [Field F]

/-- `det (b, c) (b', c') = b c' - c b'`. -/
def det (w v : F × F) : F := w.1 * v.2 - w.2 * v.1

/-- The coset `g Z_d`: the points `g · (0, t d)` for `t : F`, as coordinates. -/
def lineA (g : F × F × F) (d : F × F) : Set (F × F × F) :=
  Set.range fun t : F => (g.1 + t * det g.2 d, (g.2.1 + t * d.1, g.2.2 + t * d.2))

/-- The fibre over `w`: the points `(μ, w)` for `μ : F`. -/
def fib (w : F × F) : Set (F × F × F) :=
  Set.range fun μ : F => (μ, w)

/-- The sets that are lines: cosets `lineA g d` with `d ≠ 0`, and fibres. -/
def lineSet (F : Type*) [Field F] : Set (Set (F × F × F)) :=
  {S | (∃ g d, d ≠ 0 ∧ S = lineA g d) ∨ ∃ w, S = fib w}

/-- A line of AS(q): a set of points that lies in `lineSet`. -/
@[ext]
structure Line (F : Type*) [Field F] where
  /-- The points on the line. -/
  carrier : Set (F × F × F)
  mem_lineSet : carrier ∈ lineSet F

instance : Membership (F × F × F) (Line F) :=
  ⟨fun l p => p ∈ l.carrier⟩

theorem mem_line_iff {l : Line F} {p : F × F × F} : p ∈ l ↔ p ∈ l.carrier := Iff.rfl

instance [Finite F] : Finite (Line F) :=
  Finite.of_injective Line.carrier fun _ _ h => Line.ext h

/-- Every line is a coset or a fibre. -/
theorem Line.carrier_cases (l : Line F) :
    (∃ g d, d ≠ 0 ∧ l.carrier = lineA g d) ∨ ∃ w, l.carrier = fib w :=
  l.mem_lineSet

/-- The line `lineA g d` as a `Line`. -/
def dirLine (g : F × F × F) {d : F × F} (hd : d ≠ 0) : Line F :=
  ⟨lineA g d, Or.inl ⟨g, d, hd, rfl⟩⟩

/-- The fibre over `w` as a `Line`. -/
def fibLine (w : F × F) : Line F :=
  ⟨fib w, Or.inr ⟨w, rfl⟩⟩

theorem mem_lineA_self (g : F × F × F) (d : F × F) : g ∈ lineA g d :=
  ⟨0, by simp [det]⟩

omit [Field F] in
theorem mem_fib_iff {x : F × F × F} {w : F × F} : x ∈ fib w ↔ x.2 = w := by
  constructor
  · rintro ⟨μ, rfl⟩
    rfl
  · intro h
    exact ⟨x.1, by rw [← h]⟩

/-- Re-basing a coset at one of its own points gives the same coset. -/
theorem lineA_eq_of_mem {g x : F × F × F} {d : F × F} (hx : x ∈ lineA g d) :
    lineA x d = lineA g d := by
  obtain ⟨t₀, rfl⟩ := hx
  ext y
  simp only [lineA, Set.mem_range]
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨t₀ + s, ?_⟩
    simp only [det]
    ext <;> dsimp only <;> ring
  · rintro ⟨s, rfl⟩
    refine ⟨s - t₀, ?_⟩
    simp only [det]
    ext <;> dsimp only <;> ring

/-- Rescaling the direction does not change the coset. -/
theorem lineA_smul (g : F × F × F) {d : F × F} {s : F} (hs : s ≠ 0) :
    lineA g (s • d) = lineA g d := by
  ext y
  simp only [lineA, Set.mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t * s, ?_⟩
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ext <;> dsimp only <;> ring
  · rintro ⟨t, rfl⟩
    refine ⟨t * s⁻¹, ?_⟩
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ext <;> dsimp only <;> field_simp

/-- A vector with zero determinant against a nonzero `d` is a multiple of `d`. -/
theorem exists_smul_of_det_eq_zero {v d : F × F} (hd : d ≠ 0) (h : det v d = 0) :
    ∃ t : F, v = t • d := by
  by_cases h1 : d.1 = 0
  · have h2 : d.2 ≠ 0 := by
      intro h2; exact hd (Prod.ext h1 h2)
    have hv1 : v.1 = 0 := by
      simp only [det, h1, mul_zero, sub_zero] at h
      exact (mul_eq_zero.mp h).resolve_right h2
    refine ⟨v.2 / d.2, Prod.ext ?_ ?_⟩
    · simp [hv1, h1]
    · simp only [Prod.smul_snd, smul_eq_mul]
      field_simp
  · refine ⟨v.1 / d.1, Prod.ext ?_ ?_⟩
    · simp only [Prod.smul_fst, smul_eq_mul]
      field_simp
    · simp only [det] at h
      simp only [Prod.smul_snd, smul_eq_mul]
      rw [div_mul_eq_mul_div, eq_div_iff h1]
      linear_combination -h

end BipartiteDD.ASq
