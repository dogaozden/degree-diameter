import BipartiteDD.Haar.GraphD
import Mathlib.Tactic.Group

/-! Distance balls around the base vertices of a Haar graph, described by words.

The base vertices are `(1, A) = .inl 1` and `(1, B) = .inr 1`. By Proposition 2.2 of
`research/theorems/HAAR_D8_10.md`, the `A`-vertices at distance `2 j` from `(1, A)` are the `(x, A)` with
`x ∈ (S⁻¹S)^j`, and the `B`-vertices at distance `2 j + 1` are the `(y, B)` with `y ∈ S (S⁻¹S)^j`. The
predicates `LBall S m v` and `RBall S m v` are these descriptions, with `m` the distance.

The key step is `lBall_of_walk`: a walk of length `L` from `v` to the base gives some `k ≤ L` with
`LBall S k v`. It is an induction on the walk, one step at a time from the base. The disjunct in the
definition fixes the side of `v` from the parity of `k`, so no separate parity lemma is needed. -/

namespace BipartiteDD.LeanMaxx.HaarConv

open SimpleGraph BipartiteDD.Haar

variable {G : Type*} [Group G]

/-- The `m`-ball around `(1, A)`. An `A`-vertex `(x, A)` with `m = 2 j` and `x` a left word of `j` factors, or
a `B`-vertex `(y, B)` with `m = 2 j + 1` and `s⁻¹ y` a left word of `j` factors for some `s ∈ S`. -/
def LBall (S : Finset G) (m : ℕ) (v : G ⊕ G) : Prop :=
  (∃ j, m = 2 * j ∧ ∃ x, v = .inl x ∧ IsLeftWord S j x) ∨
    (∃ j, m = 2 * j + 1 ∧ ∃ y, v = .inr y ∧ ∃ s ∈ S, IsLeftWord S j (s⁻¹ * y))

/-- The `m`-ball around `(1, B)`. A `B`-vertex `(y, B)` with `m = 2 j` and `y` a right word of `j` factors, or an
`A`-vertex `(x, A)` with `m = 2 j + 1` and `s * x` a right word of `j` factors for some `s ∈ S`. -/
def RBall (S : Finset G) (m : ℕ) (v : G ⊕ G) : Prop :=
  (∃ j, m = 2 * j ∧ ∃ y, v = .inr y ∧ IsRightWord S j y) ∨
    (∃ j, m = 2 * j + 1 ∧ ∃ x, v = .inl x ∧ ∃ s ∈ S, IsRightWord S j (s * x))

/-! ### Words -/

theorem isLeftWord_mono {S : Finset G} {j n : ℕ} {x : G} (h : IsLeftWord S j x) (hjn : j ≤ n) :
    IsLeftWord S n x := by
  obtain ⟨w, hw, hmem, hp⟩ := h
  exact ⟨w, hw.trans hjn, hmem, hp⟩

theorem isRightWord_mono {S : Finset G} {j n : ℕ} {x : G} (h : IsRightWord S j x) (hjn : j ≤ n) :
    IsRightWord S n x := by
  obtain ⟨w, hw, hmem, hp⟩ := h
  exact ⟨w, hw.trans hjn, hmem, hp⟩

/-- Prepending the pair `(s, t)` to a left word of `j` factors gives a left word of `j + 1` factors. -/
theorem isLeftWord_cons {S : Finset G} {j : ℕ} {s t x : G} (hs : s ∈ S) (ht : t ∈ S)
    (h : IsLeftWord S j x) : IsLeftWord S (j + 1) (s⁻¹ * t * x) := by
  obtain ⟨w, hw, hmem, hp⟩ := h
  refine ⟨(s, t) :: w, by simp only [List.length_cons]; omega, ?_, ?_⟩
  · intro p hp'
    rcases List.mem_cons.mp hp' with rfl | hp'
    · exact ⟨hs, ht⟩
    · exact hmem p hp'
  · simp [hp]

/-- Prepending the pair `(s, t)` to a right word of `j` factors gives a right word of `j + 1` factors. -/
theorem isRightWord_cons {S : Finset G} {j : ℕ} {s t x : G} (hs : s ∈ S) (ht : t ∈ S)
    (h : IsRightWord S j x) : IsRightWord S (j + 1) (s * t⁻¹ * x) := by
  obtain ⟨w, hw, hmem, hp⟩ := h
  refine ⟨(s, t) :: w, by simp only [List.length_cons]; omega, ?_, ?_⟩
  · intro p hp'
    rcases List.mem_cons.mp hp' with rfl | hp'
    · exact ⟨hs, ht⟩
    · exact hmem p hp'
  · simp [hp]

/-! ### One step -/

/-- Moving one step away from the base keeps a vertex in the next ball. The step is taken from `u` to `v`, so
the claim is about `v`. -/
theorem lBall_step {S : Finset G} {m : ℕ} {u v : G ⊕ G} (hu : LBall S m u)
    (huv : (haarGraph S).Adj u v) : LBall S (m + 1) v := by
  rcases hu with ⟨j, rfl, x, rfl, hx⟩ | ⟨j, rfl, y, rfl, s, hs, hy⟩
  · rcases v with a | h
    · exact absurd huv (haarGraph_not_adj_inl_inl S x a)
    · rw [haarGraph_adj_inl_inr] at huv
      refine Or.inr ⟨j, by omega, h, rfl, h * x⁻¹, huv, ?_⟩
      have e : (h * x⁻¹)⁻¹ * h = x := by group
      rw [e]
      exact hx
  · rcases v with a | h
    · rw [haarGraph_adj_inr_inl] at huv
      have key := isLeftWord_cons huv hs hy
      have e : (y * a⁻¹)⁻¹ * s * (s⁻¹ * y) = a := by group
      rw [e] at key
      exact Or.inl ⟨j + 1, by omega, a, rfl, key⟩
    · exact absurd huv (haarGraph_not_adj_inr_inr S y h)

theorem rBall_step {S : Finset G} {m : ℕ} {u v : G ⊕ G} (hu : RBall S m u)
    (huv : (haarGraph S).Adj u v) : RBall S (m + 1) v := by
  rcases hu with ⟨j, rfl, y, rfl, hy⟩ | ⟨j, rfl, x, rfl, s, hs, hx⟩
  · rcases v with a | b
    · rw [haarGraph_adj_inr_inl] at huv
      refine Or.inr ⟨j, by omega, a, rfl, y * a⁻¹, huv, ?_⟩
      have e : y * a⁻¹ * a = y := by group
      rw [e]
      exact hy
    · exact absurd huv (haarGraph_not_adj_inr_inr S y b)
  · rcases v with a | b
    · exact absurd huv (haarGraph_not_adj_inl_inl S x a)
    · rw [haarGraph_adj_inl_inr] at huv
      have key := isRightWord_cons huv hs hx
      have e : b * x⁻¹ * s⁻¹ * (s * x) = b := by group
      rw [e] at key
      exact Or.inl ⟨j + 1, by omega, b, rfl, key⟩

/-! ### From walks to balls -/

/-- A walk of length `L` from `v` to `(1, A)` gives some `k ≤ L` with `v` in the `k`-ball. -/
theorem lBall_of_walk {S : Finset G} {v b : G ⊕ G} (r : (haarGraph S).Walk v b) :
    b = .inl 1 → ∃ k, k ≤ r.length ∧ LBall S k v := by
  induction r with
  | nil =>
    intro hb
    subst hb
    exact ⟨0, Nat.zero_le _, Or.inl ⟨0, rfl, 1, rfl, ⟨[], by simp, by simp, by simp⟩⟩⟩
  | cons h q ih =>
    intro hb
    obtain ⟨k, hk, hball⟩ := ih hb
    exact ⟨k + 1, by rw [SimpleGraph.Walk.length_cons]; omega, lBall_step hball h.symm⟩

/-- A walk of length `L` from `v` to `(1, B)` gives some `k ≤ L` with `v` in the `k`-ball. -/
theorem rBall_of_walk {S : Finset G} {v b : G ⊕ G} (r : (haarGraph S).Walk v b) :
    b = .inr 1 → ∃ k, k ≤ r.length ∧ RBall S k v := by
  induction r with
  | nil =>
    intro hb
    subst hb
    exact ⟨0, Nat.zero_le _, Or.inl ⟨0, rfl, 1, rfl, ⟨[], by simp, by simp, by simp⟩⟩⟩
  | cons h q ih =>
    intro hb
    obtain ⟨k, hk, hball⟩ := ih hb
    exact ⟨k + 1, by rw [SimpleGraph.Walk.length_cons]; omega, rBall_step hball h.symm⟩

/-- A vertex within distance `m` of `(1, A)` lies in some ball `LBall S k` with `k ≤ m`. -/
theorem exists_lBall {S : Finset G} {v : G ⊕ G} {m : ℕ}
    (h : (haarGraph S).edist v (.inl 1) ≤ (m : ENat)) : ∃ k, k ≤ m ∧ LBall S k v := by
  have hne : (haarGraph S).edist v (.inl 1) ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top m) h
  obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top hne
  have hlen : p.length ≤ m := by
    have h' : (p.length : ENat) ≤ m := by rw [hp]; exact h
    exact_mod_cast h'
  obtain ⟨k, hk, hball⟩ := lBall_of_walk p rfl
  exact ⟨k, hk.trans hlen, hball⟩

/-- A vertex within distance `m` of `(1, B)` lies in some ball `RBall S k` with `k ≤ m`. -/
theorem exists_rBall {S : Finset G} {v : G ⊕ G} {m : ℕ}
    (h : (haarGraph S).edist v (.inr 1) ≤ (m : ENat)) : ∃ k, k ≤ m ∧ RBall S k v := by
  have hne : (haarGraph S).edist v (.inr 1) ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top m) h
  obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top hne
  have hlen : p.length ≤ m := by
    have h' : (p.length : ENat) ≤ m := by rw [hp]; exact h
    exact_mod_cast h'
  obtain ⟨k, hk, hball⟩ := rBall_of_walk p rfl
  exact ⟨k, hk.trans hlen, hball⟩

end BipartiteDD.LeanMaxx.HaarConv
