import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Data.Set.Card

namespace BipartiteDD

/-- `G` is bipartite, every vertex has at most `d` neighbours, and every two vertices are joined by
a walk of length at most `D`. `ediam` is `⊤` for a disconnected graph, so the last condition also
forces connectivity. -/
def IsBipartiteDegDiam {V : Type*} (G : SimpleGraph V) (d D : ℕ) : Prop :=
  G.Colorable 2 ∧ (∀ v, (G.neighborSet v).ncard ≤ d) ∧ G.ediam ≤ D

variable {n : ℕ}

/-- The graph whose neighbour lists are `nbrs`. `fromRel` symmetrises and drops loops. -/
def graphOf (nbrs : Fin n → List (Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => v ∈ nbrs u

/-- Bitmask of the vertices within `r` steps of `v`. -/
def ball (nbrs : Fin n → List (Fin n)) : ℕ → Fin n → ℕ
  | 0, v => 2 ^ (v : ℕ)
  | r + 1, v => (nbrs v).foldl (fun acc u => acc ||| ball nbrs r u) (ball nbrs r v)

/-- The whole check. `color` is a claimed 2-colouring; the check re-verifies it. -/
def check (d D : ℕ) (nbrs : Fin n → List (Fin n)) (color : Fin n → Bool) : Bool :=
  (List.finRange n).all fun u =>
    decide ((nbrs u).length ≤ d) &&
    (nbrs u).all (fun v => decide (u ∈ nbrs v) && (color u != color v)) &&
    (ball nbrs D u == 2 ^ n - 1)

/-- Step 1: a bit is set in a fold of ORs iff it is set in the start value or in one of the terms.
Induction on `l`, using `Nat.testBit_or`. -/
theorem testBit_foldl_or (l : List (Fin n)) (f : Fin n → ℕ) (init w : ℕ) :
    (l.foldl (fun acc u => acc ||| f u) init).testBit w = true ↔
      init.testBit w = true ∨ ∃ u ∈ l, (f u).testBit w = true := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, List.mem_cons, exists_eq_or_imp,
      Bool.or_eq_true]
    tauto

/-- Step 2: every vertex marked in `ball nbrs r v` is within `r` steps of `v`.
Induction on `r`. Base: `testBit (2 ^ v) w` forces `w = v`. Step: by Step 1, either the bit is in
`ball nbrs r v` (use the hypothesis), or in `ball nbrs r u` for some `u ∈ nbrs v`. If `u = v` this is the
first case. Otherwise `v` and `u` are adjacent in `graphOf nbrs`, so the triangle inequality for `edist`
gives `edist v w ≤ 1 + r`. -/
theorem edist_le_of_testBit_ball (nbrs : Fin n → List (Fin n)) (r : ℕ) (v w : Fin n)
    (h : (ball nbrs r v).testBit w = true) : (graphOf nbrs).edist v w ≤ r := by
  induction r generalizing v with
  | zero =>
    simp only [ball, Nat.testBit_two_pow, decide_eq_true_eq] at h
    have hvw : v = w := Fin.ext h
    subst hvw
    simp [SimpleGraph.edist_self]
  | succ r ih =>
    simp only [ball, testBit_foldl_or] at h
    rcases h with h | ⟨u, hu, hw⟩
    · exact (ih v h).trans (by exact_mod_cast Nat.le_succ r)
    · have hadj : (graphOf nbrs).edist v u ≤ 1 := by
        rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
        by_cases huv : v = u
        · exact Or.inr huv
        · refine Or.inl ?_
          simp only [graphOf, SimpleGraph.fromRel_adj]
          exact ⟨huv, Or.inl hu⟩
      calc (graphOf nbrs).edist v w
          ≤ (graphOf nbrs).edist v u + (graphOf nbrs).edist u w := SimpleGraph.edist_triangle
        _ ≤ 1 + r := add_le_add hadj (ih u hw)
        _ = ((r + 1 : ℕ) : ℕ∞) := by push_cast; exact add_comm 1 (r : ℕ∞)

/-- What a passing check says about one vertex `u`: its list has at most `d` entries, every
neighbour `v` in the list has `u` in its own list and a different colour, and the ball of radius `D`
is everything. -/
theorem check_spec (d D : ℕ) (nbrs : Fin n → List (Fin n)) (color : Fin n → Bool)
    (hc : check d D nbrs color = true) (u : Fin n) :
    (nbrs u).length ≤ d ∧ (∀ v ∈ nbrs u, u ∈ nbrs v ∧ color u ≠ color v) ∧
      ball nbrs D u = 2 ^ n - 1 := by
  have hu := (List.all_eq_true.mp hc) u (List.mem_finRange u)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hu
  obtain ⟨⟨h1, h2⟩, h3⟩ := hu
  refine ⟨h1, fun v hv => ?_, h3⟩
  have h4 := List.all_eq_true.mp h2 v hv
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h4
  exact h4

/-- Step 3: if the check passes, each neighbour of `u` is in `u`'s list. Adjacency in `fromRel`
means `v ∈ nbrs u ∨ u ∈ nbrs v`; in the second case the check at `v` gives `v ∈ nbrs u`. -/
theorem mem_of_adj (d D : ℕ) (nbrs : Fin n → List (Fin n)) (color : Fin n → Bool)
    (hc : check d D nbrs color = true) {u v : Fin n} (h : (graphOf nbrs).Adj u v) : v ∈ nbrs u := by
  simp only [graphOf, SimpleGraph.fromRel_adj] at h
  rcases h.2 with h | h
  · exact h
  · exact ((check_spec d D nbrs color hc v).2.1 u h).1

/-- Step 4: soundness. -/
theorem check_sound (d D : ℕ) (nbrs : Fin n → List (Fin n)) (color : Fin n → Bool)
    (hc : check d D nbrs color = true) : IsBipartiteDegDiam (graphOf nbrs) d D := by
  refine ⟨?_, ?_, ?_⟩
  · -- Colorable 2: build a `SimpleGraph.Coloring (Fin 2)` from `color`, then use `Coloring.colorable`.
    -- Adjacent vertices get different colours: by Step 3 and the colour test in `check`.
    let C : (graphOf nbrs).Coloring (Fin 2) :=
      SimpleGraph.Coloring.mk (fun v => if color v then 1 else 0) (by
        intro v w hvw
        have hw : w ∈ nbrs v := mem_of_adj d D nbrs color hc hvw
        have hcol := ((check_spec d D nbrs color hc v).2.1 w hw).2
        by_cases hv : color v <;> by_cases hw' : color w <;> simp_all)
    exact ⟨C⟩
  · -- `neighborSet u ⊆ (nbrs u).toFinset` by Step 3, so `ncard ≤ toFinset.card ≤ length ≤ d`.
    intro v
    have hsub : (graphOf nbrs).neighborSet v ⊆ ↑(nbrs v).toFinset := by
      intro w hw
      rw [SimpleGraph.mem_neighborSet] at hw
      simp only [Finset.mem_coe, List.mem_toFinset]
      exact mem_of_adj d D nbrs color hc hw
    calc ((graphOf nbrs).neighborSet v).ncard
        ≤ (((nbrs v).toFinset : Finset (Fin n)) : Set (Fin n)).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = (nbrs v).toFinset.card := Set.ncard_coe_finset _
      _ ≤ (nbrs v).length := List.toFinset_card_le _
      _ ≤ d := (check_spec d D nbrs color hc v).1
  · -- `ediam ≤ D` iff every `edist u w ≤ D`. The check gives `ball nbrs D u = 2 ^ n - 1`, whose bit `w`
    -- is set for every `w < n` (`Nat.testBit_two_pow_sub_one`); then use Step 2.
    rw [SimpleGraph.ediam_le_iff]
    intro u w
    apply edist_le_of_testBit_ball nbrs D u w
    rw [(check_spec d D nbrs color hc u).2.2, Nat.testBit_two_pow_sub_one]
    simp only [decide_eq_true_eq]
    exact w.isLt

end BipartiteDD
