import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Diam

/-! # D = 5 formalisation, part 1: `Reach`

`Reach G a b n` says there is a walk from `a` to `b` of length at most `n`. It is the only distance notion
used in the files of this directory (`research/theorems/D5_QUADRANGLE.md`); the lemmas are those of
`HexagonD7.Reach` on the branch `claude/lean-all-jvj7b0`, re-proved here so that the directory is self-contained. -/

namespace BipartiteDD.LeanMaxx.D5

open SimpleGraph

/-- A walk of length at most `n`. -/
def Reach {W : Type*} (G : SimpleGraph W) (a b : W) (n : ℕ) : Prop := ∃ w : G.Walk a b, w.length ≤ n

section Reach

variable {W : Type*} {G : SimpleGraph W}

theorem Reach.refl (a : W) (n : ℕ) : Reach G a a n := ⟨.nil, by simp⟩

theorem Reach.adj {a b : W} (h : G.Adj a b) : Reach G a b 1 := ⟨.cons h .nil, by simp⟩

theorem Reach.mono {a b : W} {n n' : ℕ} (h : Reach G a b n) (hn : n ≤ n') : Reach G a b n' := by
  obtain ⟨w, hw⟩ := h; exact ⟨w, hw.trans hn⟩

theorem Reach.trans {a b c : W} {n n' : ℕ} (h : Reach G a b n) (h' : Reach G b c n') :
    Reach G a c (n + n') := by
  obtain ⟨w, hw⟩ := h; obtain ⟨w', hw'⟩ := h'
  exact ⟨w.append w', by rw [Walk.length_append]; omega⟩

theorem Reach.symm {a b : W} {n : ℕ} (h : Reach G a b n) : Reach G b a n := by
  obtain ⟨w, hw⟩ := h; exact ⟨w.reverse, by simpa using hw⟩

theorem Reach.map {W' : Type*} {G' : SimpleGraph W'} (f : G →g G') {a b : W} {n : ℕ}
    (h : Reach G a b n) : Reach G' (f a) (f b) n := by
  obtain ⟨w, hw⟩ := h; exact ⟨w.map f, by simpa using hw⟩

theorem Reach.edist_le {a b : W} {n : ℕ} (h : Reach G a b n) : G.edist a b ≤ n := by
  obtain ⟨w, hw⟩ := h
  exact (SimpleGraph.edist_le w).trans (by exact_mod_cast hw)

/-- Two steps through a middle vertex. -/
theorem Reach.two {a b c : W} (h1 : G.Adj a b) (h2 : G.Adj b c) : Reach G a c 2 :=
  (Reach.adj h1).trans (Reach.adj h2)

end Reach

end BipartiteDD.LeanMaxx.D5
