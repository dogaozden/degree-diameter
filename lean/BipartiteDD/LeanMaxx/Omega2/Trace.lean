import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Projected walks with switches

`B` is a graph on `β` and `π : β → β` an involution (`π a = π (σ a)` swaps a point with its partner line).
`Tr B π m s a b` says there is a walk from `a` to `b` in `B` made of `m` `B`-edges and `s` *switches*
`a ↦ π a`, in any order.

Setting for the graph `G` (on `V`) with label map `f : V → β` and copy map `c : V → Option ι`:

* `h1`: a `G`-edge between two copy vertices stays inside one copy and projects to a `B`-edge;
* `h2`: a new vertex `x` is adjacent only to copy vertices whose label is `f x` or `π (f x)`;
(Two new vertices are never adjacent: `h2` already forces the neighbours of a new vertex to be copy vertices.)

`exists_trace`: a `G`-walk between copy vertices of length `m + 2k` projects to a trace with `m`
`B`-edges and `s ≤ k` switches (a pass through a new vertex costs 2 and either stays or switches).
-/

namespace BipartiteDD.LeanMaxx.Omega2

open SimpleGraph

section Tr

variable {β : Type*} {B : SimpleGraph β} {π : β → β}

/-- Walks in `B` with edges and switches `a ↦ π a`; indices: number of edges, number of switches. -/
inductive Tr (B : SimpleGraph β) (π : β → β) : ℕ → ℕ → β → β → Prop
  | nil (a : β) : Tr B π 0 0 a a
  | edge {a b c : β} {m s : ℕ} : B.Adj a b → Tr B π m s b c → Tr B π (m + 1) s a c
  | sw {a c : β} {m s : ℕ} : Tr B π m s (π a) c → Tr B π m (s + 1) a c

theorem Tr.walk0 {m : ℕ} {a b : β} (h : Tr B π m 0 a b) : ∃ p : B.Walk a b, p.length = m := by
  generalize hs : 0 = s at h
  induction h with
  | nil a => exact ⟨.nil, rfl⟩
  | edge hab _ ih =>
    obtain ⟨p, hp⟩ := ih hs
    exact ⟨.cons hab p, by simp [hp]⟩
  | sw _ _ => omega

/-- Split at the first switch. -/
theorem Tr.decomp {m s : ℕ} {a b : β} (h : Tr B π m (s + 1) a b) :
    ∃ e m' u, m = e + m' ∧ (∃ p : B.Walk a u, p.length = e) ∧ Tr B π m' s (π u) b := by
  generalize hs : s + 1 = s' at h
  induction h generalizing s with
  | nil a => omega
  | edge hab _ ih =>
    obtain ⟨e, m', u, hm, ⟨p, hp⟩, ht⟩ := ih hs
    exact ⟨e + 1, m', u, by omega, ⟨.cons hab p, by simp [hp]⟩, ht⟩
  | @sw a c m s0 ht _ =>
    have : s0 = s := by omega
    subst this
    exact ⟨0, m, a, by omega, ⟨.nil, rfl⟩, ht⟩

theorem Tr.zero_edges {s : ℕ} {a b : β} (h : Tr B π 0 s a b) : b = π^[s] a := by
  generalize hm : 0 = m at h
  induction h with
  | nil a => rfl
  | edge _ _ _ => omega
  | @sw a c m s0 _ ih =>
    rw [Function.iterate_succ_apply]
    exact ih hm

theorem Tr.col {κ : β → ZMod 2} (hκ : ∀ u v, B.Adj u v → κ u ≠ κ v)
    (hπ : ∀ a, κ (π a) = κ a + 1) {m s : ℕ} {a b : β} (h : Tr B π m s a b) :
    κ b = κ a + (m : ZMod 2) + (s : ZMod 2) := by
  induction h with
  | nil a => simp
  | @edge a b c m s hab _ ih =>
    have : κ b = κ a + 1 := by
      have hne := hκ a b hab
      revert hne; generalize κ a = x; generalize κ b = y; revert x y; decide
    rw [ih, this]; push_cast; ring
  | @sw a c m s _ ih =>
    rw [ih, hπ]; push_cast; ring

end Tr

section Trace

variable {β V ι : Type*} {B : SimpleGraph β} {π : β → β} {G : SimpleGraph V} {f : V → β}
  {c : V → Option ι}

/-- The labels of the two ends of a pass through a new vertex `y` differ by a stay or a switch. -/
theorem pass_label (hπ : ∀ a, π (π a) = a) {l₁ l₂ y : β}
    (h1 : l₁ = y ∨ l₁ = π y) (h2 : l₂ = y ∨ l₂ = π y) : l₂ = l₁ ∨ l₂ = π l₁ := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr (hπ _).symm
  · exact Or.inl rfl

/-- Projection of a walk between copy vertices to a trace; strong induction on the length. -/
theorem exists_trace
    (h1 : ∀ u w i j, G.Adj u w → c u = some i → c w = some j → i = j ∧ B.Adj (f u) (f w))
    (h2 : ∀ x w, G.Adj x w → c x = none → c w ≠ none ∧ (f w = f x ∨ f w = π (f x)))
    (hπ : ∀ a, π (π a) = a) :
    ∀ (n : ℕ) {u v : V} (p : G.Walk u v), p.length = n → c u ≠ none → c v ≠ none →
      ∃ m k s, Tr B π m s (f u) (f v) ∧ s ≤ k ∧ p.length = m + 2 * k ∧
        (k = 0 → ∀ z ∈ p.support, c z ≠ none) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u v p hn hu hv
    cases p with
    | nil => exact ⟨0, 0, 0, Tr.nil _, le_rfl, rfl, fun _ z hz => by
        simp at hz; subst hz; exact hu⟩
    | @cons _ y _ huy p' =>
      by_cases hy : c y = none
      · -- pass through the new vertex `y`
        cases p' with
        | nil => exact absurd hy (by simpa using hv)
        | @cons _ z _ hyz p'' =>
          have hz := (h2 y z hyz hy).1
          obtain ⟨-, hlu⟩ := h2 y u huy.symm hy
          obtain ⟨-, hlz⟩ := h2 y z hyz hy
          have hlen : p''.length < n := by
            simp only [Walk.length_cons] at hn; omega
          obtain ⟨m, k, s, ht, hsk, hl, hk⟩ := ih _ hlen p'' rfl hz hv
          simp only [Walk.length_cons] at hn hl ⊢
          rcases pass_label hπ hlu hlz with hst | hsw
          · refine ⟨m, k + 1, s, ?_, by omega, by omega, by simp⟩
            rw [← hst]; exact ht
          · refine ⟨m, k + 1, s + 1, ?_, by omega, by omega, by simp⟩
            exact Tr.sw (by rw [← hsw]; exact ht)
      · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hu
        obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hy
        have hlen : p'.length < n := by simp only [Walk.length_cons] at hn; omega
        obtain ⟨m, k, s, ht, hsk, hl, hk⟩ := ih _ hlen p' rfl hy hv
        refine ⟨m + 1, k, s, Tr.edge (h1 u y i j huy hi hj).2 ht, hsk, ?_, ?_⟩
        · simp only [Walk.length_cons]; omega
        · intro hk0 z hz
          simp only [Walk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hu
          · exact hk hk0 z hz

/-- A walk through copy vertices only keeps one copy index. -/
theorem copy_index_const
    (h1 : ∀ u w i j, G.Adj u w → c u = some i → c w = some j → i = j ∧ B.Adj (f u) (f w))
    {a b : V} (p : G.Walk a b) (hcopy : ∀ w ∈ p.support, c w ≠ none)
    (i j : ι) (hi : c a = some i) (hj : c b = some j) : i = j := by
  induction p generalizing i with
  | nil => simpa [hi] using hj
  | @cons a a' _ h p ih =>
    obtain ⟨i', hi'⟩ := Option.ne_none_iff_exists'.mp (hcopy a' (by simp))
    have hstep := (h1 a a' i i' h hi hi').1
    have hrest := ih (fun w hw => hcopy w (by simp [hw])) i' hi' hj
    exact hstep.trans hrest

end Trace

end BipartiteDD.LeanMaxx.Omega2
