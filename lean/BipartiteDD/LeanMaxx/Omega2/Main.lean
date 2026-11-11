import BipartiteDD.LeanMaxx.Omega2.Reach
import Mathlib.Combinatorics.SimpleGraph.Diam

/-!
# Theorem 2: two labels per new vertex

Abstract form of Theorem 2 of `research/squads/cells/d12D8_table.md`. Let `B` be the incidence graph of a
generalized hexagon of order `(q, q)`, `q ≥ 7` (`HexData`), `κ` its 2-colouring (points / lines) and
`π` the partner map (point `t` ↔ line `σ t`: an involution swapping the classes).

`G` is a bipartite graph (colouring `K`) on `V` with label map `f : V → β` and copy map
`c : V → Option ι` (`some i` = vertex of copy `i`, `none` = new vertex):

* `h1`: a `G`-edge between two copy vertices stays inside one copy and projects to a `B`-edge;
* `h2`: a new vertex `x` is adjacent only to copy vertices carrying label `f x` or `π (f x)`
  (point `t` and line `σ t`; the switch rule: a pass through a new vertex either keeps the label or
  replaces it by its partner);
* `hsurj`: every copy contains every label; `hconn`: two vertices of a copy are joined by a walk through
  copy vertices.

Then every new vertex `x` and every copy `j` that `x` does not meet are at distance `≥ 9`
from some vertex of copy `j` (`omega2_far`), so `G` has diameter `≥ 9 = D₁ + 3` (`omega2_ediam`).
No assumption on how many labels a new vertex really meets, nor on how the copies are glued (any mix of
blocks, any colour convention per copy).
-/

set_option linter.unusedSectionVars false

namespace BipartiteDD.LeanMaxx.Omega2

open SimpleGraph

variable {β V ι : Type*}

/-- `K + κ ∘ f` is constant along a walk through copy vertices. -/
theorem eps_walk {B : SimpleGraph β} {G : SimpleGraph V} {f : V → β} {c : V → Option ι}
    {κ : β → ZMod 2} {K : V → ZMod 2} (hK : ∀ u v, G.Adj u v → K u ≠ K v)
    (hκ : ∀ u v, B.Adj u v → κ u ≠ κ v)
    (h1 : ∀ u w i j, G.Adj u w → c u = some i → c w = some j → i = j ∧ B.Adj (f u) (f w))
    {a b : V} (p : G.Walk a b) (hcopy : ∀ z ∈ p.support, c z ≠ none) :
    K b + κ (f b) = K a + κ (f a) := by
  induction p with
  | nil => rfl
  | @cons a a' b h p ih =>
    obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp (hcopy a (by simp))
    obtain ⟨i', hi'⟩ := Option.ne_none_iff_exists'.mp (hcopy a' (by simp))
    have hB := (h1 a a' i i' h hi hi').2
    have e1 := hK a a' h
    have e2 := hκ _ _ hB
    rw [ih (fun z hz => hcopy z (by simp [hz]))]
    revert e1 e2
    generalize K a = x1; generalize K a' = x2; generalize κ (f a) = y1; generalize κ (f a') = y2
    revert x1 x2 y1 y2; decide

theorem omega2_far [Fintype β] [DecidableEq β] {B : SimpleGraph β} [DecidableRel B.Adj] {q : ℕ}
    {κ : β → ZMod 2} (H : HexData B q κ) (hq : 7 ≤ q) {π : β → β} (hπ : ∀ a, π (π a) = a)
    (hκπ : ∀ a, κ (π a) = κ a + 1)
    {G : SimpleGraph V} {f : V → β} {c : V → Option ι} {K : V → ZMod 2}
    (hK : ∀ u v, G.Adj u v → K u ≠ K v)
    (h1 : ∀ u w i j, G.Adj u w → c u = some i → c w = some j → i = j ∧ B.Adj (f u) (f w))
    (h2 : ∀ x w, G.Adj x w → c x = none → c w ≠ none ∧ (f w = f x ∨ f w = π (f x)))
    (hsurj : ∀ j s, ∃ v, c v = some j ∧ f v = s)
    (hconn : ∀ j u v, c u = some j → c v = some j →
      ∃ p : G.Walk u v, ∀ z ∈ p.support, c z ≠ none)
    {x : V} (hx : c x = none) {j : ι} (hmiss : ∀ w, G.Adj x w → c w ≠ some j) :
    ∃ v, c v = some j ∧ (9 : ℕ∞) ≤ G.edist x v := by
  -- the invariant `ε` of copy `j`
  obtain ⟨v0, hv0, -⟩ := hsurj j (f x)
  set ε : ZMod 2 := K v0 + κ (f v0) with hεdef
  have hε : ∀ v, c v = some j → K v + κ (f v) = ε := by
    intro v hv
    obtain ⟨p, hp⟩ := hconn j v0 v hv0 hv
    exact eps_walk hK H.col h1 p hp
  -- the label `a` among `f x`, `π (f x)` of the class `K x + 1 + ε`
  obtain ⟨a, haκ, hlab⟩ : ∃ a, κ a = K x + 1 + ε ∧
      ∀ l, (l = f x ∨ l = π (f x)) → (l = a ∨ l = π a) := by
    by_cases hcase : κ (f x) = K x + 1 + ε
    · refine ⟨f x, hcase, ?_⟩
      rintro l (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
    · refine ⟨π (f x), ?_, ?_⟩
      · rw [hκπ]
        revert hcase; generalize κ (f x) = y; generalize K x = z; generalize ε = e
        revert y z e; decide
      · rintro l (rfl | rfl)
        · exact Or.inr (hπ _).symm
        · exact Or.inl rfl
  obtain ⟨w, hdw, hnw⟩ := H.exists_far (π := π) hq a
  obtain ⟨v, hvc, hvf⟩ := hsurj j w
  have hκw : κ w = κ a := by
    have := col_dist H.col (H.reach a w)
    rw [hdw] at this
    rw [this]
    have h6 : ((6 : ℕ) : ZMod 2) = 0 := by decide
    rw [h6, add_zero]
  have hKv : K v = K x + 1 := by
    have e1 := hε v hvc
    rw [hvf, hκw, haκ] at e1
    revert e1; generalize K v = y; generalize K x = z; generalize ε = e
    revert y z e; decide
  refine ⟨v, hvc, ?_⟩
  unfold SimpleGraph.edist
  refine le_iInf fun p => ?_
  by_contra hlt
  have hlt' : p.length ≤ 8 := by
    have : (p.length : ℕ∞) < 9 := not_le.mp hlt
    have : p.length < 9 := by exact_mod_cast this
    omega
  cases p with
  | nil => rw [hvc] at hx; simp at hx
  | @cons _ u0 _ hxu p' =>
    obtain ⟨hu0, hlu0⟩ := h2 x u0 hxu hx
    have hv_ne : c v ≠ none := by rw [hvc]; simp
    obtain ⟨m, k, s, ht, hsk, hl, hk⟩ := exists_trace h1 h2 hπ _ p' rfl hu0 hv_ne
    have hk1 : 1 ≤ k := by
      by_contra hk0
      have hk0' : k = 0 := by omega
      obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hu0
      have hij := copy_index_const h1 p' (hk hk0') i j hi hvc
      subst hij
      exact hmiss u0 hxu hi
    -- parity: the walk has odd length
    have hpar := walk_col hK (SimpleGraph.Walk.cons hxu p')
    rw [hKv] at hpar
    have hodd : (((SimpleGraph.Walk.cons hxu p').length : ℕ) : ZMod 2) = 1 := by
      revert hpar; generalize K x = y; generalize (((SimpleGraph.Walk.cons hxu p').length : ℕ) : ZMod 2) = t
      revert y t; decide
    simp only [SimpleGraph.Walk.length_cons, hl] at hodd hlt'
    have hm : Even m := by
      rw [← ZMod.natCast_eq_zero_iff_even]
      push_cast at hodd
      revert hodd; generalize (m : ZMod 2) = t; generalize (k : ZMod 2) = u; revert t u; decide
    obtain ⟨r, hr⟩ := hm
    have hb : m + 2 * k ≤ 6 := by omega
    rw [hvf] at ht
    exact hnw (H.reach_bad hπ hκπ hdw (hlab _ hlu0) ht ⟨r, hr⟩ hsk hk1 hb)

/-- **Theorem 2** (abstract form): the graph has diameter at least `9`. -/
theorem omega2_ediam [Fintype β] [DecidableEq β] {B : SimpleGraph β} [DecidableRel B.Adj] {q : ℕ}
    {κ : β → ZMod 2} (H : HexData B q κ) (hq : 7 ≤ q) {π : β → β} (hπ : ∀ a, π (π a) = a)
    (hκπ : ∀ a, κ (π a) = κ a + 1)
    {G : SimpleGraph V} {f : V → β} {c : V → Option ι} {K : V → ZMod 2}
    (hK : ∀ u v, G.Adj u v → K u ≠ K v)
    (h1 : ∀ u w i j, G.Adj u w → c u = some i → c w = some j → i = j ∧ B.Adj (f u) (f w))
    (h2 : ∀ x w, G.Adj x w → c x = none → c w ≠ none ∧ (f w = f x ∨ f w = π (f x)))
    (hsurj : ∀ j s, ∃ v, c v = some j ∧ f v = s)
    (hconn : ∀ j u v, c u = some j → c v = some j →
      ∃ p : G.Walk u v, ∀ z ∈ p.support, c z ≠ none)
    {x : V} (hx : c x = none) {j : ι} (hmiss : ∀ w, G.Adj x w → c w ≠ some j) :
    (9 : ℕ∞) ≤ G.ediam := by
  obtain ⟨v, -, hv⟩ := omega2_far H hq hπ hκπ hK h1 h2 hsurj hconn hx hmiss
  exact hv.trans edist_le_ediam

end BipartiteDD.LeanMaxx.Omega2
