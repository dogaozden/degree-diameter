import BipartiteDD.HexagonD7.Family
import BipartiteDD.LeanMaxx.D7Family.Hub

/-! The three-level theorem with `q² + 1` freed points (research/theorems/D7_HEXAGON.md, Cor. 8.1 and 9.1).

`d7_of_sets`: let `F` be a finite field with `q = |F| ≥ 5`, `R` a set of `q² + 1` points of `H(q)` whose
representatives are pairwise non-orthogonal for the polar form `Bf` (a partial ovoid of `Q(6, q)`; by the
orthogonality property (F4) these points are pairwise opposite in `H(q)`), and `S` a set of `q² + 1` lines
pairwise at distance `6` (a partial spread). Then there is a bipartite graph of maximum degree `q + 2` and
diameter at most `7` on `6 N(q) + 2 (q² + 1)` vertices, `N(q) = (q + 1)(1 + q² + q⁴)`.
The local duality is `exists_local_duality`, the hubs are the `q² + 1` nodes of the hub tree of `Hub.lean`
on each side, the graph is the one of `HexagonD7.exists_graph` (Theorem 1 of the hexagon-family project). -/

namespace BipartiteDD.LeanMaxx.D7Family

open SimpleGraph Finset BipartiteDD.Hexagon BipartiteDD.HexagonD7
open scoped Classical

variable {F : Type*} [Field F]

set_option linter.unusedSectionVars false

/-- Collinear points: the second lies in the plane of the first. -/
theorem mem_plane_of_coll {r p : SPt F} (h : Coll (hexInc (F := F)) r p) :
    p.1.rep ∈ plane r.1.rep := by
  obtain ⟨-, W, h1, h2⟩ := h
  have hp : IsHPair r.1.rep p.1.rep := W.2.2 _ h1 _ h2
  exact (isHPair_iff_mem_plane r.1.rep_nonzero r.2).1 hp

theorem bf_eq_zero_of_coll {r p : SPt F} (h : Coll (hexInc (F := F)) r p) : Bf r.1.rep p.1.rep = 0 := by
  obtain ⟨-, W, h1, h2⟩ := h
  exact (W.2.2 _ h1 _ h2).2.2.1

/-- Points with non-orthogonal representatives have disjoint closed 2-balls. -/
theorem disjoint_ballP {r s : SPt F} [Fintype (SPt F)] [Fintype (HLine F)] (hne : r ≠ s) (hb : Bf r.1.rep s.1.rep ≠ 0) :
    Disjoint (ballP (hexInc (F := F)) r) (ballP (hexInc (F := F)) s) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  rw [mem_ballP] at hz hz'
  have hb' : Bf s.1.rep r.1.rep ≠ 0 := by rwa [Bf_comm]
  rcases hz with rfl | hz <;> rcases hz' with rfl | hz'
  · exact hne rfl
  · exact hb' (bf_eq_zero_of_coll hz')
  · exact hb (bf_eq_zero_of_coll hz)
  · exact hb (Bf_eq_zero_of_mem_plane z.1.rep_nonzero (mem_plane_of_coll hz.symm)
      (mem_plane_of_coll hz'.symm))

/-- Opposite lines have disjoint closed 2-balls. -/
theorem disjoint_ballL {a b : HLine F} [Fintype (SPt F)] [Fintype (HLine F)] (hne : a ≠ b)
    (hopp : HexagonD.Opp (hexInc (F := F)) a b) :
    Disjoint (ballL (hexInc (F := F)) a) (ballL (hexInc (F := F)) b) := by
  rw [Finset.disjoint_left]
  intro m hm hm'
  rw [mem_ballL] at hm hm'
  rcases hm with h | ⟨-, p, h1, h2⟩ <;> rcases hm' with h' | ⟨-, p', h3, h4⟩
  · exact hne (h.symm.trans h')
  · rw [h] at h4
    exact hopp ⟨p', a, p', h4, h4, h4, h3⟩
  · rw [h'] at h2
    exact hopp ⟨p, b, p, h1, h2, h2, h2⟩
  · exact hopp ⟨p, m, p', h1, h2, h4, h3⟩


section Main

variable [Fintype F]

/-- **The three-level theorem with `q² + 1` freed points.** -/
theorem d7_of_sets (hq : 5 ≤ Fintype.card F) (R : Finset (SPt F)) (S : Finset (HLine F))
    (hRc : R.card = Fintype.card F ^ 2 + 1) (hSc : S.card = Fintype.card F ^ 2 + 1)
    (hR : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → Bf r.1.rep s.1.rep ≠ 0)
    (hS : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → HexagonD.Opp (hexInc (F := F)) a b) :
    ∃ G : SimpleGraph (Fin (6 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) +
        2 * (Fintype.card F ^ 2 + 1))), IsBipartiteDegDiam G (Fintype.card F + 2) 7 := by
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
  have hR' : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → Disjoint (ballP (hexInc (F := F)) r) (ballP (hexInc (F := F)) s) :=
    fun r hr s hs hne => disjoint_ballP hne (hR r hr s hs hne)
  have hS' : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Disjoint (ballL (hexInc (F := F)) a) (ballL (hexInc (F := F)) b) :=
    fun a ha b hb hne => disjoint_ballL hne (hS a ha b hb hne)
  let τ : R ≃ S := Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hRc, hSc])
  obtain ⟨σ, -, hσ⟩ := exists_local_duality hdig hP hL hR' hS' τ hcL.symm
  -- the hubs
  obtain ⟨d, hd⟩ : ∃ d, q = d + 2 := ⟨q - 2, by omega⟩
  have hd3 : 3 ≤ d := by omega
  have hm : 3 * d + 4 ≤ d * d * d := by nlinarith
  obtain ⟨par, hfib⟩ := exists_par hm
  have hcN : Fintype.card (Node d (3 * d + 4)) = Fintype.card R := by
    rw [Node.card_node, Fintype.card_coe, hRc, hd]; ring
  let e : Node d (3 * d + 4) ≃ R := Fintype.equivOfCardEq hcN
  let own : Node d (3 * d + 4) → SPt F := fun v => (e v).1
  have H : Hyp hexInc σ (↑R : Set (SPt F)) own own (NS par) := {
    pl := pl_of_polygon hG,
    p2 := p2_of_polygon hG,
    l2 := l2_of_polygon hG,
    r1 := by
      intro r hr s hs hcoll
      exact Finset.disjoint_left.1 (hR' r hr s hs hcoll.1) (mem_ballP.2 (Or.inr hcoll)) (self_mem_ballP s),
    r2 := fun r hr p => hσ r hr p,
    ownV_mem := fun v => (e v).2,
    ownU_mem := fun u => (e u).2,
    r3V := fun v v' => Or.inr (reach_VV par v v'),
    r3U := fun u u' => Or.inr (reach_UU par u u') }
  have hown : ∀ r, (univ.filter (fun v : Node d (3 * d + 4) => own v = r)).card ≤ 1 := by
    intro r
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    simp only [mem_filter, mem_univ, true_and, own] at ha hb
    exact e.injective (Subtype.ext (ha.trans hb.symm))
  have hNS : ∀ v : Node d (3 * d + 4), (univ.filter (NS par v)).card ≤ q - 1 := fun v => by
    have := card_NS_left par hfib v; omega
  have hNS' : ∀ u : Node d (3 * d + 4), (univ.filter (fun v => NS par v u)).card ≤ q - 1 := fun u => by
    have := card_NS_right par hfib u; omega
  have main := exists_graph (q := q) (j := 1) H (fun p => by convert (hP p).le)
    (fun l => by convert (hL l).le) (fun r => by convert hown r) (fun r => by convert hown r)
    (fun v => by convert hNS v) (fun u => by convert hNS' u) hq1
  have ecard : (2 * 1 + 1) * (Fintype.card (SPt F) + Fintype.card (HLine F)) +
      Fintype.card (Node d (3 * d + 4)) + Fintype.card (Node d (3 * d + 4)) =
      6 * ((q + 1) * (1 + q ^ 2 + q ^ 4)) + 2 * (q ^ 2 + 1) := by
    rw [hcL, hcP, hcN, Fintype.card_coe, hRc]; ring
  rw [ecard, show q + 1 + 1 = q + 2 by ring] at main
  exact main

end Main

end BipartiteDD.LeanMaxx.D7Family
