import BipartiteDD.GQ4.Main

/-! Group Doubling, part 1: the diameter condition (c) of Delorme's doubling theorem.

For a graph `G`, a set `A` of vertices (the doubled set) and a bound `D`, condition (c) says: for all `x`,
`y` in one component of `G[A]` (`x = y` allowed) there is a vertex `z ∉ A` with
`d(x, z) + d(z, y) ≤ D`. Lemma `exists_mid` extends this to every pair `x`, `y` at distance at most `D`:
there is always a vertex `z ∉ A` on a walk of length at most `D` from `x` to `y`, or satisfying (c). This
is the only place where (c) enters the diameter proofs; the rest is the "sheet" argument. -/

namespace BipartiteDD.Doubling

open SimpleGraph
open scoped Classical

variable {V : Type*}

/-- Condition (c): any two vertices of one component of `G[A]` (possibly equal) have a common vertex `z`
outside `A` with `d(x, z) + d(z, y) ≤ D`. -/
def CondC (G : SimpleGraph V) (A : Set V) (D : ℕ) : Prop :=
  ∀ (x y : V) (hx : x ∈ A) (hy : y ∈ A), (G.induce A).Reachable ⟨x, hx⟩ ⟨y, hy⟩ →
    ∃ z, z ∉ A ∧ G.edist x z + G.edist z y ≤ D

variable {G : SimpleGraph V} {A : Set V} {D : ℕ}

/-- If `x`, `y` are at distance at most `D` and (c) holds, some `z ∉ A` has `d(x, z) + d(z, y) ≤ D`.
If `x` or `y` is outside `A`, take it as `z`. If they lie in one component of `G[A]`, use (c). Otherwise a
shortest walk from `x` to `y` leaves `A` somewhere, and splitting it there gives `z`. -/
theorem exists_mid (hc : CondC G A D) {x y : V} (hxy : G.edist x y ≤ D) :
    ∃ z, z ∉ A ∧ G.edist x z + G.edist z y ≤ D := by
  by_cases hx : x ∈ A
  swap
  · exact ⟨x, hx, by simpa using hxy⟩
  by_cases hy : y ∈ A
  swap
  · exact ⟨y, hy, by simpa using hxy⟩
  by_cases hr : (G.induce A).Reachable ⟨x, hx⟩ ⟨y, hy⟩
  · exact hc x y hx hy hr
  have hne : G.edist x y ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top D) hxy
  obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top hne
  by_cases hall : ∀ z ∈ p.support, z ∈ A
  · exact (hr ⟨p.induce A hall⟩).elim
  push Not at hall
  obtain ⟨z, hz, hzA⟩ := hall
  refine ⟨z, hzA, ?_⟩
  have h1 : G.edist x z ≤ (p.takeUntil z hz).length := edist_le _
  have h2 : G.edist z y ≤ (p.dropUntil z hz).length := edist_le _
  have h3 : (p.takeUntil z hz).length + (p.dropUntil z hz).length = p.length := by
    conv_rhs => rw [← p.take_spec hz]
    rw [Walk.length_append]
  calc G.edist x z + G.edist z y
      ≤ ((p.takeUntil z hz).length : ℕ∞) + (p.dropUntil z hz).length := add_le_add h1 h2
    _ = (p.length : ℕ∞) := by exact_mod_cast h3
    _ = G.edist x y := hp
    _ ≤ D := hxy

end BipartiteDD.Doubling
