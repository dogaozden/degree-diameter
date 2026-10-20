import BipartiteDD.HexagonD.TheoremD
import BipartiteDD.Regular.TheoremR

/-! Theorem D, slice 2, part 22 (target 5): the levelled doubling of an incidence graph as a bipartite
relation.

For an incidence structure `inc : P → L → Prop` and heights `h : P ⊕ L → ℕ`, the versions of points are
`VerL = Σ p, (Fin (h p) → Fin m)`, the versions of lines `VerR`, and `rel` is the incidence of versions
(`inc` and prefix-comparable strings). `biGraph rel` is the levelled doubling of `incGraph inc`
(`biGraph_rel_eq`), so the degree and diameter bounds of the doubling theorem transfer
(`isBipartiteDegDiam_biGraph_rel`). -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonD

open BipartiteDD.Doubling BipartiteDD.Regular

section Generic

variable {P L : Type*} {inc : P → L → Prop} {m : ℕ} {h : P ⊕ L → ℕ}

/-- Versions of points. -/
abbrev VerL (P L : Type*) (m : ℕ) (h : P ⊕ L → ℕ) : Type _ := Σ p : P, (Fin (h (.inl p)) → Fin m)

/-- Versions of lines. -/
abbrev VerR (P L : Type*) (m : ℕ) (h : P ⊕ L → ℕ) : Type _ := Σ l : L, (Fin (h (.inr l)) → Fin m)

/-- Incidence of versions. -/
def rel (inc : P → L → Prop) (m : ℕ) (h : P ⊕ L → ℕ) (a : VerL P L m h) (b : VerR P L m h) : Prop :=
  inc a.1 b.1 ∧ Agree a.2 b.2

/-- The versions of the vertices of `P ⊕ L` are the versions of points and of lines. -/
def verEquiv (P L : Type*) (m : ℕ) (h : P ⊕ L → ℕ) : Ver (P ⊕ L) m h ≃ VerL P L m h ⊕ VerR P L m h :=
  Equiv.sumSigmaDistrib _

theorem biGraph_rel_eq (inc : P → L → Prop) (m : ℕ) (h : P ⊕ L → ℕ) :
    biGraph (rel inc m h) = (levelled (Hexagon.incGraph inc) m h).comap (verEquiv P L m h).symm := by
  ext u v
  rcases u with a | b <;> rcases v with a' | b'
  · simp [verEquiv, levelled]
  · simp [verEquiv, levelled, rel]
    intro _
    exact Iff.rfl
  · simp [verEquiv, levelled, rel, and_comm]
    intro _
    exact ⟨fun h => Agree.symm h, fun h => Agree.symm h⟩
  · simp [verEquiv, levelled]

theorem isBipartiteDegDiam_biGraph_rel {Δ D : ℕ}
    (hH : IsBipartiteDegDiam (levelled (Hexagon.incGraph inc) m h) Δ D) :
    IsBipartiteDegDiam (biGraph (rel inc m h)) Δ D := by
  rw [biGraph_rel_eq]
  exact isBipartiteDegDiam_comap (verEquiv P L m h) hH

end Generic

end BipartiteDD.HexagonD
