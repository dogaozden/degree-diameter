import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Sphere sizes in graphs of bounded degree (the counting step of Theorem 4.1 of
`research/theorems/HAAR_D8_10.md`, §4.1).

If every vertex has at most `Δ` neighbours, the vertices at distance exactly `m + 1` from `v` number at
most `Δ (Δ - 1)^m`. Each vertex at distance `m + 1` has a neighbour at distance `m`; each vertex `u` at
distance `m + 1 ≥ 1` has one such parent, so at most `Δ - 1` of its neighbours lie at distance `m + 2`. -/

namespace BipartiteDD.LeanMaxx.HaarBound

open Finset SimpleGraph

variable {V : Type*} [Fintype V]

/-- The vertices at distance exactly `L` from `v`. -/
noncomputable def sphere (H : SimpleGraph V) (v : V) (L : ℕ) : Finset V :=
  univ.filter fun w => H.edist v w = (L : ℕ∞)

theorem mem_sphere {H : SimpleGraph V} {v w : V} {L : ℕ} :
    w ∈ sphere H v L ↔ H.edist v w = (L : ℕ∞) := by
  simp [sphere]

omit [Fintype V] in
/-- A vertex `u` at distance `m + 1` from `v` has a neighbour `x` at distance exactly `m`. -/
theorem exists_pred (H : SimpleGraph V) {v u : V} {m : ℕ} (h : H.edist v u = ((m + 1 : ℕ) : ℕ∞)) :
    ∃ x, H.Adj u x ∧ H.edist v x = (m : ℕ∞) := by
  have hr : H.edist u v = ((m + 1 : ℕ) : ℕ∞) := by rw [SimpleGraph.edist_comm]; exact h
  obtain ⟨q, hq⟩ := exists_walk_of_edist_eq_coe hr
  cases q with
  | nil => simp at hq
  | cons hux q' =>
    rename_i x
    refine ⟨x, hux, ?_⟩
    have hlen : q'.length = m := by simp only [Walk.length_cons] at hq; omega
    have hle : H.edist v x ≤ (m : ℕ∞) := by
      have h1 := H.edist_le q'.reverse
      rw [Walk.length_reverse, hlen] at h1
      exact h1
    have h2 : H.edist v u ≤ H.edist v x + H.edist x u := H.edist_triangle
    have h3 : H.edist x u = 1 := by
      rw [SimpleGraph.edist_comm]
      exact edist_eq_one_iff_adj.mpr hux
    rw [h, h3] at h2
    have hfin : H.edist v x ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top m) hle
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [← hn] at hle h2 ⊢
    norm_cast at hle h2 ⊢
    omega

theorem card_sphere_zero (H : SimpleGraph V) (v : V) : (sphere H v 0).card ≤ 1 := by
  have hsub : sphere H v 0 ⊆ {v} := by
    intro w hw
    rw [mem_sphere, Nat.cast_zero, edist_eq_zero_iff] at hw
    simp [hw]
  exact (card_le_card hsub).trans (by simp)

theorem card_sphere_one_le (H : SimpleGraph V) [DecidableRel H.Adj] (Δ : ℕ)
    (hΔ : ∀ u, (H.neighborFinset u).card ≤ Δ) (v : V) :
    (sphere H v 1).card ≤ Δ := by
  have hsub : sphere H v 1 ⊆ H.neighborFinset v := by
    intro w hw
    rw [mem_sphere, Nat.cast_one, edist_eq_one_iff_adj] at hw
    rw [mem_neighborFinset]
    exact hw
  exact (card_le_card hsub).trans (hΔ v)

/-- The step of the count: a vertex at distance `m + 2` has at most `Δ - 1` ways to be reached
from the layer at distance `m + 1`, since each layer vertex `u` already has a parent at distance `m`. -/
theorem card_sphere_succ_le [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] (Δ : ℕ)
    (hΔ : ∀ u, (H.neighborFinset u).card ≤ Δ) (v : V) (m : ℕ) :
    (sphere H v (m + 1 + 1)).card ≤ (Δ - 1) * (sphere H v (m + 1)).card := by
  have hsub : sphere H v (m + 1 + 1) ⊆ (sphere H v (m + 1)).biUnion fun u =>
      (H.neighborFinset u).filter fun w => H.edist v w = ((m + 1 + 1 : ℕ) : ℕ∞) := by
    intro w hw
    rw [mem_sphere] at hw
    obtain ⟨x, hwx, hx⟩ := exists_pred H hw
    rw [Finset.mem_biUnion]
    refine ⟨x, mem_sphere.mpr hx, ?_⟩
    rw [Finset.mem_filter, mem_neighborFinset]
    exact ⟨hwx.symm, hw⟩
  calc (sphere H v (m + 1 + 1)).card
      ≤ ((sphere H v (m + 1)).biUnion fun u =>
          (H.neighborFinset u).filter fun w => H.edist v w = ((m + 1 + 1 : ℕ) : ℕ∞)).card :=
        card_le_card hsub
    _ ≤ ∑ u ∈ sphere H v (m + 1),
          ((H.neighborFinset u).filter fun w => H.edist v w = ((m + 1 + 1 : ℕ) : ℕ∞)).card :=
        card_biUnion_le
    _ ≤ ∑ u ∈ sphere H v (m + 1), (Δ - 1) := by
        refine Finset.sum_le_sum fun u hu => ?_
        rw [mem_sphere] at hu
        obtain ⟨q, hqu, hq⟩ := exists_pred H hu
        have hsub' : (H.neighborFinset u).filter (fun w => H.edist v w = ((m + 1 + 1 : ℕ) : ℕ∞)) ⊆
            (H.neighborFinset u).erase q := by
          intro w hw
          rw [Finset.mem_filter] at hw
          rw [Finset.mem_erase]
          refine ⟨?_, hw.1⟩
          rintro rfl
          have h : (m + 1 + 1 : ℕ) = m := by exact_mod_cast (hw.2.symm.trans hq)
          omega
        calc ((H.neighborFinset u).filter fun w => H.edist v w = ((m + 1 + 1 : ℕ) : ℕ∞)).card
            ≤ ((H.neighborFinset u).erase q).card := card_le_card hsub'
          _ = (H.neighborFinset u).card - 1 := card_erase_of_mem ((H.mem_neighborFinset u q).mpr hqu)
          _ ≤ Δ - 1 := Nat.sub_le_sub_right (hΔ u) 1
    _ = (Δ - 1) * (sphere H v (m + 1)).card := by
        rw [sum_const, smul_eq_mul, mul_comm]

/-- Sphere bound: `|S_{m+1}(v)| ≤ Δ (Δ - 1)^m` when every vertex has at most `Δ` neighbours. -/
theorem card_sphere_le [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] (Δ : ℕ)
    (hΔ : ∀ u, (H.neighborFinset u).card ≤ Δ) (v : V) (m : ℕ) :
    (sphere H v (m + 1)).card ≤ Δ * (Δ - 1) ^ m := by
  induction m with
  | zero =>
    simpa using card_sphere_one_le H Δ hΔ v
  | succ m ih =>
    calc (sphere H v (m + 1 + 1)).card
        ≤ (Δ - 1) * (sphere H v (m + 1)).card := card_sphere_succ_le H Δ hΔ v m
      _ ≤ (Δ - 1) * (Δ * (Δ - 1) ^ m) := Nat.mul_le_mul_left _ ih
      _ = Δ * (Δ - 1) ^ (m + 1) := by ring

end BipartiteDD.LeanMaxx.HaarBound
