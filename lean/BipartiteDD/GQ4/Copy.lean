import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import BipartiteDD.GQ4.Diam

/-! Group GQ4, part 3: copies of vertices, in generality.

Let `G` be a graph on `W` and `r : V → W` send each vertex of `V` to its underlying vertex.
A vertex `x` is *original* when `orig x`, and `s` is a section: `r (s w) = w`, with `s w` original.
The copy graph has `x ~ y` iff `r x ~ r y` in `G` and at least one of `x, y` is original. So
copies are adjacent only to originals, and two copies of the same vertex are not adjacent.

Main result: if `G` has diameter at most `4` and every vertex of `G` has a neighbour, then the
copy graph has diameter at most `4`. -/

namespace BipartiteDD.GQ4

open SimpleGraph

section Generic

variable {V W : Type*}

/-- Copies: `x ~ y` iff `r x ~ r y` in `G`, and at least one of `x, y` is original. -/
def copyGraph (G : SimpleGraph W) (r : V → W) (orig : V → Prop) : SimpleGraph V where
  Adj x y := G.Adj (r x) (r y) ∧ (orig x ∨ orig y)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

variable {G : SimpleGraph W} {r : V → W} {orig : V → Prop} {s : W → V}

/-- Walks in `G` whose first and last vertex are original-adjacent lift to copy-walks of the same
length, with the intermediate vertices replaced by their originals. -/
theorem edist_le_length_of_orig (hs : ∀ w, r (s w) = w) (hso : ∀ w, orig (s w)) :
    ∀ {a b : W} (p : G.Walk a b) (x y : V), r x = a → r y = b → 0 < p.length →
      (orig x ∨ orig y) → (copyGraph G r orig).edist x y ≤ p.length := by
  intro a b p
  induction p with
  | nil => intro x y _ _ h; simp at h
  | @cons a c b h' p' ih =>
    intro x y hx hy _ hO
    cases p' with
    | nil =>
      have hadj : (copyGraph G r orig).Adj x y := ⟨by rw [hx, hy]; exact h', hO⟩
      exact (edist_le (Walk.cons hadj Walk.nil)).trans (by simp)
    | cons h'' p'' =>
      have hadj : (copyGraph G r orig).Adj x (s c) := ⟨by rw [hs, hx]; exact h', Or.inr (hso c)⟩
      have h1 : (copyGraph G r orig).edist x (s c) ≤ 1 :=
        (edist_le (Walk.cons hadj Walk.nil)).trans (by simp)
      have h2 := ih (s c) y (hs c) hy (by simp) (Or.inl (hso c))
      calc (copyGraph G r orig).edist x y
          ≤ (copyGraph G r orig).edist x (s c) + (copyGraph G r orig).edist (s c) y :=
            SimpleGraph.edist_triangle
        _ ≤ 1 + ((Walk.cons h'' p'').length : ℕ∞) := add_le_add h1 h2
        _ = ((Walk.cons h' (Walk.cons h'' p'')).length : ℕ∞) := by
            simp only [Walk.length_cons]
            push_cast
            ring

/-- Two vertices over the same underlying vertex are at distance at most `2`, through the
original over any neighbour of it. -/
theorem edist_le_two_of_fiber (hs : ∀ w, r (s w) = w) (hso : ∀ w, orig (s w))
    (hnb : ∀ w, ∃ u, G.Adj w u) {x y : V} (h : r x = r y) :
    (copyGraph G r orig).edist x y ≤ 2 := by
  obtain ⟨c, hc⟩ := hnb (r x)
  have h1 : (copyGraph G r orig).Adj x (s c) := ⟨by rw [hs]; exact hc, Or.inr (hso c)⟩
  have h2 : (copyGraph G r orig).Adj (s c) y :=
    ⟨by rw [hs, ← h]; exact hc.symm, Or.inl (hso c)⟩
  exact (edist_le (Walk.cons h1 (Walk.cons h2 Walk.nil))).trans (by simp)

/-- Two copies over the endpoints of an edge of `G` are at distance at most `3`. -/
theorem edist_le_three_of_adj (hs : ∀ w, r (s w) = w) (hso : ∀ w, orig (s w))
    (hnb : ∀ w, ∃ u, G.Adj w u) {a b : W} (h : G.Adj a b) {x y : V}
    (hx : r x = a) (hy : r y = b) : (copyGraph G r orig).edist x y ≤ 3 := by
  have h1 : (copyGraph G r orig).Adj x (s b) := ⟨by rw [hs, hx]; exact h, Or.inr (hso b)⟩
  have h2 : (copyGraph G r orig).edist (s b) y ≤ 2 :=
    edist_le_two_of_fiber hs hso hnb (by rw [hs, hy])
  calc (copyGraph G r orig).edist x y
      ≤ (copyGraph G r orig).edist x (s b) + (copyGraph G r orig).edist (s b) y :=
        SimpleGraph.edist_triangle
    _ ≤ 1 + 2 := add_le_add ((edist_le (Walk.cons h1 Walk.nil)).trans (by simp)) h2
    _ = 3 := by norm_num

/-- A walk of positive length `k` in `G` lifts to a copy-walk of length `max 3 k`. -/
theorem edist_le_max_three (hs : ∀ w, r (s w) = w) (hso : ∀ w, orig (s w))
    (hnb : ∀ w, ∃ u, G.Adj w u) :
    ∀ {a b : W} (p : G.Walk a b) (x y : V), r x = a → r y = b → 0 < p.length →
      (copyGraph G r orig).edist x y ≤ max 3 p.length := by
  intro a b p
  induction p with
  | nil => intro x y _ _ h; simp at h
  | @cons a c b h' p' ih =>
    intro x y hx hy _
    cases p' with
    | nil =>
      by_cases hO : orig x ∨ orig y
      · have hadj : (copyGraph G r orig).Adj x y := ⟨by rw [hx, hy]; exact h', hO⟩
        exact (edist_le (Walk.cons hadj Walk.nil)).trans (by simp)
      · exact (edist_le_three_of_adj hs hso hnb h' hx hy).trans (by simp)
    | cons h'' p'' =>
      have hadj : (copyGraph G r orig).Adj x (s c) := ⟨by rw [hs, hx]; exact h', Or.inr (hso c)⟩
      have h1 : (copyGraph G r orig).edist x (s c) ≤ 1 :=
        (edist_le (Walk.cons hadj Walk.nil)).trans (by simp)
      have h2 := edist_le_length_of_orig hs hso (Walk.cons h'' p'') (s c) y (hs c) hy
        (by simp) (Or.inl (hso c))
      calc (copyGraph G r orig).edist x y
          ≤ (copyGraph G r orig).edist x (s c) + (copyGraph G r orig).edist (s c) y :=
            SimpleGraph.edist_triangle
        _ ≤ 1 + ((Walk.cons h'' p'').length : ℕ∞) := add_le_add h1 h2
        _ = ((Walk.cons h' (Walk.cons h'' p'')).length : ℕ∞) := by
            simp only [Walk.length_cons]
            push_cast
            ring
        _ ≤ ((max 3 (Walk.cons h' (Walk.cons h'' p'')).length : ℕ) : ℕ∞) := by
            exact_mod_cast le_max_right _ _

/-- The copy graph has diameter at most `4` when `G` does, and every vertex of `G` has a
neighbour. -/
theorem ediam_le_four_of_copy (hs : ∀ w, r (s w) = w) (hso : ∀ w, orig (s w))
    (hnb : ∀ w, ∃ u, G.Adj w u) (hG : G.ediam ≤ 4) :
    (copyGraph G r orig).ediam ≤ 4 := by
  rw [ediam_le_iff]
  intro x y
  by_cases hxy : r x = r y
  · exact (edist_le_two_of_fiber hs hso hnb hxy).trans (by norm_num)
  · have h4 : G.edist (r x) (r y) ≤ 4 := edist_le_ediam.trans hG
    have hne : G.edist (r x) (r y) ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) h4
    obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top hne
    have hlen : p.length ≤ 4 := by
      have h : (p.length : ℕ∞) ≤ 4 := hp ▸ h4
      exact_mod_cast h
    have hpos : 0 < p.length := by
      rcases Nat.eq_zero_or_pos p.length with h0 | h0
      · exact absurd (p.eq_of_length_eq_zero h0) hxy
      · exact h0
    have hmax : max 3 p.length ≤ 4 := max_le (by norm_num) hlen
    exact (edist_le_max_three hs hso hnb p x y rfl rfl hpos).trans (by exact_mod_cast hmax)

end Generic

end BipartiteDD.GQ4
