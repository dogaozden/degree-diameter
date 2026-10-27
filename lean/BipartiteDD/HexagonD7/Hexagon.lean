import BipartiteDD.HexagonD7.Main
import BipartiteDD.HexagonEven.Main

/-! Diameter 7 from a generalized hexagon, part 5: generalized hexagons and `H(q)`.

`hyp_empty`: in the incidence graph of a generalized hexagon (`GenPolygonGraph _ 6`) the walk hypotheses of
Theorem 1 hold. `table_family`: for every finite field `F` (`q = |F|`) and `0 ≤ j ≤ q`, the `2j+1`-level
construction over the split Cayley hexagon `H(q)` with no freed point is a bipartite graph of maximum degree
`q + 1 + j` and diameter at most `7` on `2(2j+1)(q+1)(q⁴+q²+1)` vertices: the D = 7 table values
(Delorme–Gómez–Quisquater for `j = 1`). -/

namespace BipartiteDD.HexagonD7

open SimpleGraph Finset BipartiteDD.Hexagon
open scoped Classical

section Polygon

variable {P L : Type*} {inc : P → L → Prop}

/-- (F1): in a generalized hexagon every point is joined to every line by a walk of length at most `5`. -/
theorem pl_of_polygon (hG : Doubling.GenPolygonGraph (Hexagon.incGraph inc) 6) (p : P) (l : L) :
    Reach (Hexagon.incGraph inc) (.inl p) (.inr l) 5 := by
  have hd : (Hexagon.incGraph inc).edist (.inl p) (.inr l) ≤ 6 := by
    have := (Hexagon.incGraph inc).edist_le_ediam (u := .inl p) (v := .inr l)
    rw [hG.ediam] at this
    exact_mod_cast this
  have hne : (Hexagon.incGraph inc).edist (.inl p) (.inr l) ≠ ⊤ :=
    ne_top_of_le_ne_top (by exact ENat.coe_ne_top 6) hd
  obtain ⟨w, hw⟩ := (SimpleGraph.edist_ne_top_iff_reachable.1 hne).exists_walk_length_eq_edist
  refine ⟨w, ?_⟩
  have h6 : w.length ≤ 6 := by
    have : (w.length : ℕ∞) ≤ 6 := hw ▸ hd
    exact_mod_cast this
  have hodd : ¬ Even w.length := by
    have := (isLeft_eq_iff_even w)
    simp at this
    exact Nat.not_even_iff_odd.2 this
  rcases Nat.even_or_odd w.length with he | ⟨k, hk⟩
  · exact absurd he hodd
  · omega

/-- (F2) for points. -/
theorem p2_of_polygon (hG : Doubling.GenPolygonGraph (Hexagon.incGraph inc) 6) (p : P) :
    ∃ l l', l ≠ l' ∧ inc p l ∧ inc p l' := by
  obtain ⟨a, b, ha, hb, hab⟩ := hG.deg (.inl p)
  rcases a with a | l <;> rcases b with b | l'
  · exact absurd ha Hexagon.incGraph_not_adj_inl_inl
  · exact absurd ha Hexagon.incGraph_not_adj_inl_inl
  · exact absurd hb Hexagon.incGraph_not_adj_inl_inl
  · exact ⟨l, l', fun h => hab (by rw [h]), ha, hb⟩

/-- (F2) for lines. -/
theorem l2_of_polygon (hG : Doubling.GenPolygonGraph (Hexagon.incGraph inc) 6) (l : L) :
    ∃ p p', p ≠ p' ∧ inc p l ∧ inc p' l := by
  obtain ⟨a, b, ha, hb, hab⟩ := hG.deg (.inr l)
  rcases a with p | a <;> rcases b with p' | b
  · exact ⟨p, p', fun h => hab (by rw [h]), ha, hb⟩
  · exact absurd hb Hexagon.incGraph_not_adj_inr_inr
  · exact absurd ha Hexagon.incGraph_not_adj_inr_inr
  · exact absurd ha Hexagon.incGraph_not_adj_inr_inr

/-- The hypotheses of Theorem 1 with no freed point and no hub. -/
theorem hyp_empty (hG : Doubling.GenPolygonGraph (Hexagon.incGraph inc) 6) (σ : P ≃ L) :
    Hyp inc σ ∅ (Empty.elim : Empty → P) (Empty.elim : Empty → P) (fun _ _ => False) where
  pl := pl_of_polygon hG
  p2 := p2_of_polygon hG
  l2 := l2_of_polygon hG
  r1 := fun r hr => absurd hr (Set.notMem_empty r)
  r2 := fun r hr => absurd hr (Set.notMem_empty r)
  ownV_mem := fun v => v.elim
  ownU_mem := fun u => u.elim
  r3V := fun v => v.elim
  r3U := fun u => u.elim

end Polygon

section Hq

variable {F : Type*} [Field F] [Fintype F]

/-- **The table family at D = 7.** For every finite field `F` with `q = |F|` and every `j ≤ q`:
`n_b(q + 1 + j, 7) ≥ 2(2j + 1)(q + 1)(q⁴ + q² + 1)`, from `2j + 1` copies of `H(q)` joined by `j` shifted
copies of a bijection points → lines. -/
theorem table_family (j : ℕ) (hj : j ≤ Fintype.card F) :
    ∃ G : SimpleGraph (Fin (2 * (2 * j + 1) *
        ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)))),
      IsBipartiteDegDiam G (Fintype.card F + 1 + j) 7 := by
  letI : Fintype (SPt F) := Fintype.ofFinite _
  letI : Fintype (HLine F) := haveI := HexagonEven.finite_hline_even (F := F); Fintype.ofFinite _
  have hG := HexagonEven.genPolygonGraph_hexagon_even (F := F)
  have hP : ∀ p : SPt F, (univ.filter (hexInc p)).card = Fintype.card F + 1 := fun p => by
    rw [← HexagonEven.card_lines_through_even p, Nat.card_eq_fintype_card, Fintype.card_subtype]; rfl
  have hL : ∀ l : HLine F, (univ.filter (fun p => hexInc p l)).card = Fintype.card F + 1 := fun l => by
    rw [← card_points_hline l, Nat.card_eq_fintype_card, Fintype.card_subtype]; rfl
  have hcP : Fintype.card (SPt F) = (Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4) := by
    rw [← card_spt_eq, Nat.card_eq_fintype_card]
  have hcL : Fintype.card (HLine F) = Fintype.card (SPt F) := by
    have := card_lines_eq (inc := hexInc (F := F)) (k := Fintype.card F + 1) (by omega)
      (fun p => by rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; exact hP p)
      (fun l => by rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; exact hL l)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this
    exact this
  let σ : SPt F ≃ HLine F := Fintype.equivOfCardEq hcL.symm
  have main := exists_graph (q := Fintype.card F) (j := j) (hyp_empty hG σ)
    (fun p => (hP p).le) (fun l => (hL l).le) (fun r => by simp) (fun r => by simp)
    (fun v => v.elim) (fun u => u.elim) hj
  have e : (2 * j + 1) * (Fintype.card (SPt F) + Fintype.card (HLine F)) + Fintype.card Empty +
      Fintype.card Empty = 2 * (2 * j + 1) *
        ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) := by
    rw [hcL, hcP]; simp; ring
  rw [e] at main
  exact main

end Hq

end BipartiteDD.HexagonD7
