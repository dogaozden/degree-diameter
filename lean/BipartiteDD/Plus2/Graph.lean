import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Tactic.NormNum

/-! The generic diameter lemma (REPORT.md section 4, Step 0): in a bipartite graph whose
left vertices pairwise have a common neighbour and whose right vertices pairwise have a
common neighbour, every two vertices are at distance at most 3.

The graph lives on an arbitrary type `W`, related to the sum `α ⊕ β` of points and lines by an
equivalence `e`, so the lemma applies both to the incidence graph itself and to its transport
along a bijection with `Fin n`. -/

namespace BipartiteDD.Plus2
open SimpleGraph

theorem ediam_le_three {α β W : Type*} (H : SimpleGraph W) (e : α ⊕ β ≃ W) (inc : α → β → Prop)
    (hG : ∀ a b, H.Adj (e (.inl a)) (e (.inr b)) ↔ inc a b)
    (hPP : ∀ p q : α, p ≠ q → ∃ l, inc p l ∧ inc q l)
    (hLL : ∀ l m : β, l ≠ m → ∃ p, inc p l ∧ inc p m)
    (hL : ∀ l : β, ∃ p, inc p l) : H.ediam ≤ 3 := by
  -- a point and a line: walk p – l′ – p′ – l of length at most 3
  have key : ∀ (p : α) (l : β), H.edist (e (.inl p)) (e (.inr l)) ≤ 3 := by
    intro p l
    by_cases h : inc p l
    · exact (edist_le (Walk.cons ((hG p l).2 h) Walk.nil)).trans (by norm_num)
    · obtain ⟨q, hq⟩ := hL l
      have hpq : p ≠ q := fun e' => h (e' ▸ hq)
      obtain ⟨m, hpm, hqm⟩ := hPP p q hpq
      exact (edist_le (Walk.cons ((hG p m).2 hpm)
        (Walk.cons ((hG q m).2 hqm).symm (Walk.cons ((hG q l).2 hq) Walk.nil)))).trans (by norm_num)
  rw [ediam_le_iff]
  intro w₁ w₂
  obtain ⟨u, rfl⟩ := e.surjective w₁
  obtain ⟨v, rfl⟩ := e.surjective w₂
  rcases u with p | l <;> rcases v with q | m
  · by_cases hpq : p = q
    · subst hpq
      simp
    · obtain ⟨l, h1, h2⟩ := hPP p q hpq
      exact (edist_le (Walk.cons ((hG p l).2 h1)
        (Walk.cons ((hG q l).2 h2).symm Walk.nil))).trans (by norm_num)
  · exact key p m
  · rw [edist_comm]
    exact key q l
  · by_cases hlm : l = m
    · subst hlm
      simp
    · obtain ⟨p, h1, h2⟩ := hLL l m hlm
      exact (edist_le (Walk.cons ((hG p l).2 h1).symm
        (Walk.cons ((hG p m).2 h2) Walk.nil))).trans (by norm_num)

end BipartiteDD.Plus2
