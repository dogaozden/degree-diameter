import BipartiteDD.HexagonD7.LocalDual
import BipartiteDD.HexagonD7.Hexagon
import BipartiteDD.HexagonD.Polygon

/-! Diameter 7 from a generalized hexagon, part 9: freed points in every `H(q)`.

`freed_family`: for every finite field `F` with `q = |F|`, there is a bipartite graph of maximum degree `q + 2` and
diameter at most `7` with `6(q+1)(q⁴+q²+1) + 2(q - 1)` vertices, i.e. `2(q - 1)` more than the table value
`3·|I(H(q))|`. The `q - 1` freed points and lines are pairwise opposite (greedy, `exists_disjoint_balls*`, using
`(q-1)(q²+q+1)² < (q+1)(q⁴+q²+1)`), `σ` is the local duality of Lemma 2, and the hub graph is complete bipartite
`K_{q-1,q-1}` (degree `q - 1`, same-side distance `2`). -/

namespace BipartiteDD.HexagonD7

open SimpleGraph Finset BipartiteDD.Hexagon
open scoped Classical

variable {F : Type*} [Field F] [Fintype F]

theorem greedy_ineq (q : ℕ) (hq : 1 ≤ q) :
    (q - 1) * (1 + (q + 1) * q) ^ 2 < (q + 1) * (1 + q ^ 2 + q ^ 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  have key : (m + 1 + 1) * (1 + (m + 1) ^ 2 + (m + 1) ^ 4) =
      m * (1 + (m + 1 + 1) * (m + 1)) ^ 2 + (2 * m ^ 2 + 6 * m + 6) := by ring
  rw [show m + 1 - 1 = m by omega, key]
  exact Nat.lt_add_of_pos_right (by positivity)

/-- **Freed points in `H(q)`**: `n_b(q + 2, 7) ≥ 6(q+1)(q⁴+q²+1) + 2(q - 1)` for every finite field. -/
theorem freed_family :
    ∃ G : SimpleGraph (Fin (6 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) +
        2 * (Fintype.card F - 1))),
      IsBipartiteDegDiam G (Fintype.card F + 2) 7 := by
  letI : Fintype (SPt F) := Fintype.ofFinite _
  letI : Fintype (HLine F) := haveI := HexagonEven.finite_hline_even (F := F); Fintype.ofFinite _
  set q := Fintype.card F with hqdef
  have hq1 : 1 ≤ q := Fintype.card_pos
  have hG := HexagonEven.genPolygonGraph_hexagon_even (F := F)
  have hP : ∀ p : SPt F, (univ.filter (hexInc p)).card = q + 1 := fun p => by
    rw [← HexagonEven.card_lines_through_even p, Nat.card_eq_fintype_card, Fintype.card_subtype]; rfl
  have hL : ∀ l : HLine F, (univ.filter (fun p => hexInc p l)).card = q + 1 := fun l => by
    rw [← card_points_hline l, Nat.card_eq_fintype_card, Fintype.card_subtype]; rfl
  have hcP : Fintype.card (SPt F) = (q + 1) * (1 + q ^ 2 + q ^ 4) := by
    rw [← card_spt_eq, Nat.card_eq_fintype_card]
  have hcL : Fintype.card (HLine F) = Fintype.card (SPt F) := by
    have := card_lines_eq (inc := hexInc (F := F)) (k := q + 1) (by omega)
      (fun p => by rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; exact hP p)
      (fun l => by rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; exact hL l)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this
    exact this
  have hdig : ∀ {p r : SPt F} {M₁ M₂ : HLine F}, p ≠ r → hexInc p M₁ → hexInc r M₁ → hexInc p M₂ →
      hexInc r M₂ → M₁ = M₂ := fun hpr h1 h1' h2 h2' => HexagonD.eq_of_digon hG hpr h1 h1' h2 h2'
  have hineq := greedy_ineq q hq1
  obtain ⟨R, hRc, hR⟩ := exists_disjoint_ballsP hdig hP hL (q - 1) (by rw [hcP]; exact hineq)
  obtain ⟨S, hSc, hS⟩ := exists_disjoint_ballsL hdig hP hL (q - 1) (by rw [hcL, hcP]; exact hineq)
  let τ : R ≃ S := Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hRc, hSc])
  obtain ⟨σ, -, hσ⟩ := exists_local_duality hdig hP hL hR hS τ hcL.symm
  let own : R → SPt F := Subtype.val
  have H : Hyp hexInc σ (↑R : Set (SPt F)) own own (fun _ _ => True) := {
    pl := pl_of_polygon hG,
    p2 := p2_of_polygon hG,
    l2 := l2_of_polygon hG,
    r1 := by
      intro r hr s hs hcoll
      exact Finset.disjoint_left.1 (hR r hr s hs hcoll.1) (mem_ballP.2 (Or.inr hcoll)) (self_mem_ballP s),
    r2 := fun r hr p => hσ r hr p,
    ownV_mem := fun v => v.2,
    ownU_mem := fun u => u.2,
    r3V := by
      intro v v'
      right
      have h1 : (hubGraph (fun _ _ => True : R → R → Prop)).Adj (.inl v) (.inr v) :=
        (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl trivial⟩
      have h2 : (hubGraph (fun _ _ => True : R → R → Prop)).Adj (.inr v) (.inl v') :=
        (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inr trivial⟩
      exact ((Reach.adj h1).trans (Reach.adj h2)).mono (by norm_num),
    r3U := by
      intro u u'
      right
      have h1 : (hubGraph (fun _ _ => True : R → R → Prop)).Adj (.inr u) (.inl u) :=
        (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inr trivial⟩
      have h2 : (hubGraph (fun _ _ => True : R → R → Prop)).Adj (.inl u) (.inr u') :=
        (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl trivial⟩
      exact ((Reach.adj h1).trans (Reach.adj h2)).mono (by norm_num) }
  have hown : ∀ r, (univ.filter (fun v : R => own v = r)).card ≤ 1 := by
    intro r
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    simp only [mem_filter, mem_univ, true_and] at ha hb
    exact Subtype.ext (ha.trans hb.symm)
  have hNS : ∀ v : R, (univ.filter (fun _ : R => True)).card ≤ q - 1 := by
    intro v; rw [filter_true, card_univ, Fintype.card_coe, hRc]
  have main := exists_graph (q := q) (j := 1) H (fun p => by convert (hP p).le)
    (fun l => by convert (hL l).le) (fun r => by convert hown r) (fun r => by convert hown r)
    (fun v => by convert hNS v) (fun u => by convert hNS u) hq1
  have e : (2 * 1 + 1) * (Fintype.card (SPt F) + Fintype.card (HLine F)) + Fintype.card R +
      Fintype.card R = 6 * ((q + 1) * (1 + q ^ 2 + q ^ 4)) + 2 * (q - 1) := by
    rw [hcL, hcP, Fintype.card_coe, hRc]; ring
  rw [e, show q + 1 + 1 = q + 2 by ring] at main
  exact main

end BipartiteDD.HexagonD7
