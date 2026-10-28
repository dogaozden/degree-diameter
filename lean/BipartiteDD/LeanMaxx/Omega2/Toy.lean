import BipartiteDD.LeanMaxx.Omega2.Main

/-!
# The hypotheses of `omega2_ediam` are satisfiable

A small connected-by-new-vertices example over any `B` with `HexData`: three copies `Fin 3 × β` of `B` and
new vertices `(r, t)`, `r : Fin 2`, joined to the vertex labelled `t` in copy `r` and to the vertex
labelled `π t` in copy `r + 1` (so new vertices meet *two different labels*, and miss one copy).
All hypotheses of `omega2_ediam` hold, with `x = (0, t)` and `j = 2`.
-/

set_option linter.unusedSectionVars false

namespace BipartiteDD.LeanMaxx.Omega2

open SimpleGraph

variable {β : Type*} (B : SimpleGraph β) (π : β → β)

/-- Three copies of `B` plus two layers of new vertices. -/
def toyAdj : (Fin 3 × β) ⊕ (Fin 2 × β) → (Fin 3 × β) ⊕ (Fin 2 × β) → Prop
  | .inl (i, s), .inl (j, s') => i = j ∧ B.Adj s s'
  | .inl (i, s), .inr (r, t) => (i.val = r.val ∧ s = t) ∨ (i.val = r.val + 1 ∧ s = π t)
  | .inr (r, t), .inl (i, s) => (i.val = r.val ∧ s = t) ∨ (i.val = r.val + 1 ∧ s = π t)
  | .inr _, .inr _ => False

def toyGraph : SimpleGraph ((Fin 3 × β) ⊕ (Fin 2 × β)) where
  Adj := toyAdj B π
  symm := ⟨fun a b h => by
    rcases a with ⟨i, s⟩ | ⟨r, t⟩ <;> rcases b with ⟨j, s'⟩ | ⟨r', t'⟩ <;> simp only [toyAdj] at h ⊢
    · exact ⟨h.1.symm, (B.adj_comm _ _).mp h.2⟩
    · exact h
    · exact h⟩
  loopless := ⟨fun a h => by
    rcases a with ⟨i, s⟩ | ⟨r, t⟩ <;> simp only [toyAdj] at h
    exact B.loopless.irrefl _ h.2⟩

/-- Labels, copy map, colouring of the toy graph. -/
def toyF : (Fin 3 × β) ⊕ (Fin 2 × β) → β := Sum.elim (fun a => a.2) (fun a => a.2)

def toyC : (Fin 3 × β) ⊕ (Fin 2 × β) → Option (Fin 3) := Sum.elim (fun a => some a.1) (fun _ => none)

def toyK (κ : β → ZMod 2) : (Fin 3 × β) ⊕ (Fin 2 × β) → ZMod 2 :=
  Sum.elim (fun a => κ a.2 + (a.1.val : ZMod 2)) (fun a => κ a.2 + (a.1.val : ZMod 2) + 1)

theorem toy_walk {s s' : β} (p : B.Walk s s') (j : Fin 3) :
    ∃ g : (toyGraph B π).Walk (.inl (j, s)) (.inl (j, s')), ∀ z ∈ g.support, toyC z ≠ none := by
  induction p with
  | nil => exact ⟨.nil, by simp [toyC]⟩
  | @cons a b c h p ih =>
    obtain ⟨g, hg⟩ := ih
    have hadj : (toyGraph B π).Adj (.inl (j, a)) (.inl (j, b)) := ⟨rfl, h⟩
    refine ⟨.cons hadj g, ?_⟩
    intro z hz
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · simp [toyC]
    · exact hg z hz

theorem omega2_toy [Fintype β] [DecidableEq β] {B : SimpleGraph β} [DecidableRel B.Adj] {q : ℕ}
    {κ : β → ZMod 2} (H : HexData B q κ) (hq : 7 ≤ q) {π : β → β} (hπ : ∀ a, π (π a) = a)
    (hκπ : ∀ a, κ (π a) = κ a + 1) (t : β) :
    (9 : ℕ∞) ≤ (toyGraph B π).ediam := by
  have hr := H.reach
  -- an adjacency between a copy vertex and a new vertex
  have key : ∀ (i : Fin 3) (s : β) (r : Fin 2) (t : β), (toyGraph B π).Adj (.inl (i, s)) (.inr (r, t)) →
      (s = t ∧ (i.val : ZMod 2) = r.val) ∨ (s = π t ∧ (i.val : ZMod 2) = r.val + 1) := by
    intro i s r t h
    simp only [toyGraph, toyAdj] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h2, by rw [h1]⟩
    · exact Or.inr ⟨h2, by rw [h1]; push_cast; rfl⟩
  refine omega2_ediam (G := toyGraph B π) (f := toyF) (c := toyC) (K := toyK κ) (π := π) (x := .inr (0, t))
    (j := 2) H hq hπ hκπ ?_ ?_ ?_ ?_ ?_ rfl ?_
  · -- proper colouring
    intro u v h
    rcases u with ⟨i, s⟩ | ⟨r, t⟩ <;> rcases v with ⟨i', s'⟩ | ⟨r', t'⟩
    · simp only [toyGraph, toyAdj] at h
      obtain ⟨rfl, hB⟩ := h
      have := H.col _ _ hB
      simp only [toyK, Sum.elim_inl]
      revert this; generalize κ s = a; generalize κ s' = b; generalize (i.val : ZMod 2) = c
      revert a b c; decide
    · rcases key i s r' t' h with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
      · simp only [toyK, Sum.elim_inl, Sum.elim_inr, h2]
        generalize κ s = a; generalize (r'.val : ZMod 2) = c; revert a c; decide
      · simp only [toyK, Sum.elim_inl, Sum.elim_inr, h2, hκπ]
        generalize κ t' = a; generalize (r'.val : ZMod 2) = c; revert a c; decide
    · have h' : (toyGraph B π).Adj (.inl (i', s')) (.inr (r, t)) := h.symm
      rcases key i' s' r t h' with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
      · simp only [toyK, Sum.elim_inl, Sum.elim_inr, h2]
        generalize κ s' = a; generalize (r.val : ZMod 2) = c; revert a c; decide
      · simp only [toyK, Sum.elim_inl, Sum.elim_inr, h2, hκπ]
        generalize κ t = a; generalize (r.val : ZMod 2) = c; revert a c; decide
    · simp [toyGraph, toyAdj] at h
  · -- copy edges
    intro u w i j h hu hw
    rcases u with ⟨i₀, s⟩ | ⟨r, t⟩ <;> rcases w with ⟨j₀, s'⟩ | ⟨r', t'⟩ <;>
      simp only [toyC, Sum.elim_inl, Sum.elim_inr, Option.some.injEq, reduceCtorEq] at hu hw
    · simp only [toyGraph, toyAdj] at h
      subst hu; subst hw
      exact ⟨h.1, h.2⟩
  · -- new vertices meet two labels
    intro x w h hx
    rcases x with ⟨i, s⟩ | ⟨r, t⟩
    · simp [toyC] at hx
    · rcases w with ⟨j, s'⟩ | ⟨r', t'⟩
      · have h' : (toyGraph B π).Adj (.inl (j, s')) (.inr (r, t)) := h.symm
        rcases key j s' r t h' with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact ⟨by simp [toyC], Or.inl rfl⟩
        · exact ⟨by simp [toyC], Or.inr rfl⟩
      · simp [toyGraph, toyAdj] at h
  · -- every copy contains every label
    intro j s
    exact ⟨.inl (j, s), rfl, rfl⟩
  · -- copies are connected
    intro j u v hu hv
    rcases u with ⟨i₀, s⟩ | ⟨r, t⟩ <;> rcases v with ⟨j₀, s'⟩ | ⟨r', t'⟩ <;>
      simp only [toyC, Sum.elim_inl, Sum.elim_inr, Option.some.injEq, reduceCtorEq] at hu hv
    obtain ⟨p⟩ := hr s s'
    subst hu; subst hv
    exact toy_walk B π p _
  · -- the new vertex `(0, t)` misses copy `2`
    intro w h
    rcases w with ⟨j, s'⟩ | ⟨r', t'⟩
    · have h' : (toyGraph B π).Adj (.inl (j, s')) (.inr (0, t)) := h.symm
      simp only [toyGraph, toyAdj] at h'
      simp only [toyC, Sum.elim_inl]
      intro hj
      have := Option.some.inj hj
      subst this
      simp at h'
    · simp [toyC]

end BipartiteDD.LeanMaxx.Omega2
