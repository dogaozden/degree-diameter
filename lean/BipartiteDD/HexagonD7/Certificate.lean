import BipartiteDD.HexagonD7.Family

/-! Diameter 7 from a generalized hexagon, part 10: a certificate theorem for `H(q)`.

`certificate`: for every finite field `F` (`q = |F|`), every set `R` of points of `H(q)` with pairwise disjoint
closed 2-balls (pairwise opposite points), every set `S` of lines with the same property and `|S| = |R|`, and every
bipartite hub graph `NS` on `R ⊕ R` with degrees `≤ q - 1` and same-side distances `≤ 6`, there is a bipartite graph
of maximum degree `q + 2` and diameter `≤ 7` on `6(q+1)(q⁴+q²+1) + 2|R|` vertices. So a record of this kind is proved
once the three finite conditions (on `R`, on `S`, on `NS`) are checked. -/

namespace BipartiteDD.HexagonD7

open SimpleGraph Finset BipartiteDD.Hexagon
open scoped Classical

variable {F : Type*} [Field F] [Fintype F]

theorem certificate [Fintype (SPt F)] [Fintype (HLine F)] (R : Finset (SPt F)) (S : Finset (HLine F))
    (hR : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → Disjoint (ballP hexInc r) (ballP hexInc s))
    (hS : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Disjoint (ballL hexInc a) (ballL hexInc b))
    (hRS : R.card = S.card) (NS : R → R → Prop)
    (hNV : ∀ v, (univ.filter (NS v)).card ≤ Fintype.card F - 1)
    (hNU : ∀ u, (univ.filter (fun v => NS v u)).card ≤ Fintype.card F - 1)
    (hV6 : ∀ v v', Reach (hubGraph NS) (.inl v) (.inl v') 6)
    (hU6 : ∀ u u', Reach (hubGraph NS) (.inr u) (.inr u') 6) :
    ∃ G : SimpleGraph (Fin (6 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) +
        2 * R.card)),
      IsBipartiteDegDiam G (Fintype.card F + 2) 7 := by
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
  let τ : R ≃ S := Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hRS])
  obtain ⟨σ, -, hσ⟩ := exists_local_duality hdig hP hL hR hS τ hcL.symm
  let own : R → SPt F := Subtype.val
  have H : Hyp hexInc σ (↑R : Set (SPt F)) own own NS := {
    pl := pl_of_polygon hG,
    p2 := p2_of_polygon hG,
    l2 := l2_of_polygon hG,
    r1 := by
      intro r hr s hs hcoll
      exact Finset.disjoint_left.1 (hR r hr s hs hcoll.1) (mem_ballP.2 (Or.inr hcoll)) (self_mem_ballP s),
    r2 := fun r hr p => hσ r hr p,
    ownV_mem := fun v => v.2,
    ownU_mem := fun u => u.2,
    r3V := fun v v' => Or.inr (hV6 v v'),
    r3U := fun u u' => Or.inr (hU6 u u') }
  have hown : ∀ r, (univ.filter (fun v : R => own v = r)).card ≤ 1 := by
    intro r
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    simp only [mem_filter, mem_univ, true_and] at ha hb
    exact Subtype.ext (ha.trans hb.symm)
  have main := exists_graph (q := q) (j := 1) H (fun p => by convert (hP p).le)
    (fun l => by convert (hL l).le) (fun r => by convert hown r) (fun r => by convert hown r)
    (fun v => by convert hNV v) (fun u => by convert hNU u) hq1
  have e : (2 * 1 + 1) * (Fintype.card (SPt F) + Fintype.card (HLine F)) + Fintype.card R +
      Fintype.card R = 6 * ((q + 1) * (1 + q ^ 2 + q ^ 4)) + 2 * R.card := by
    rw [hcL, hcP, Fintype.card_coe]; ring
  rw [e, show q + 1 + 1 = q + 2 by ring] at main
  exact main

end BipartiteDD.HexagonD7
