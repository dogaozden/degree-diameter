import BipartiteDD.HexagonD.RegHex6

/-! Theorem D, slice 2, part 29 (target 5): **Theorem R**, the regular hexagon doubling.

`hex_levelled_bound`: the levelled doubling of `H(q)` (exact whiskers) has maximum degree `≤ q + m` and diameter
`≤ 6`. `theoremR`: for `m ≥ 2` there is a `(q + m)`-regular bipartite graph of diameter `≤ 6` on
`2 (q + 1) (q⁴ + q² + 1) + 2 (m - 1)((q³ + 1)(q + 1) + m (q + 1))` vertices. -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon BipartiteDD.Doubling BipartiteDD.Regular
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)] {c : F} {c0 c1 : F} {m : ℕ}

local notation "GH" => Hexagon.incGraph (hexInc (F := F))

theorem hex_levelled_bound (hc : ¬ IsSquare (-c)) (hG : GoodCubic c c0 c1) (hm : 0 < m) :
    IsBipartiteDegDiam (levelled GH m (hgt c c0 c1)) (Fintype.card F + 1 + (m - 1)) 6 := by
  have hW := wset_whiskers hc hG
  have : Fintype (SPt F ⊕ HLine F) := Fintype.ofFinite _
  have hG0 : IsBipartiteDegDiam GH (Fintype.card F + 1) 6 :=
    ⟨genPolygonGraph_hexagon.colorable, fun x => by
      rcases x with p | l
      · rw [ncard_neighborSet_inl]
      · rw [ncard_neighborSet_inr], genPolygonGraph_hexagon.ediam.le⟩
  have hF : ForestDiam GH (lev c (vStd : HLine F) (Wset c c0 c1) 0) 4 :=
    forestDiam_pi hc (A := lev c (vStd : HLine F) (Wset c c0 c1) 0) (fun p => by simp [lev, A0])
      (fun l hl => by simp [lev, A0, hl])
  exact isBipartiteDegDiam_levelled (A := lev c (vStd : HLine F) (Wset c c0 c1)) (K := 3) hm hG0
    (lev_antitone (c := c) _ (vStd_inPi c) _) (lev_three _ _) (lev_ha1 (v := vS c) hc)
    (lev_ha2 (v := vS c) hc) (lev_hb (v := vS c) hc hW) (genPolygonGraph_hexagon.condC_of_forestDiam hF)

theorem hbig_arith (q m s' : ℕ) (hq : 2 ≤ q) (hm : 2 ≤ m)
    (hS : s' + (m - 1) * m * q = (m - 1) * m * (q ^ 3 + m)) :
    2 * (m - 1) * (q + m + (m - 1) + 1) < (q + 1) * s' := by
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hS ⊢
  have ht : 1 ≤ t := by omega
  have hq3 : 4 * q ≤ q ^ 3 := by
    have h4 : 4 ≤ q ^ 2 := by nlinarith
    calc 4 * q ≤ q ^ 2 * q := Nat.mul_le_mul_right q h4
      _ = q ^ 3 := by ring
  obtain ⟨y, hy⟩ : ∃ y, y + q = q ^ 3 + (t + 1) := ⟨q ^ 3 + (t + 1) - q, by omega⟩
  have hs : s' = t * (t + 1) * y := by
    have : s' + t * (t + 1) * q = t * (t + 1) * y + t * (t + 1) * q := by
      rw [hS, ← hy]; ring
    omega
  have hy2 : 3 * q + 2 ≤ y := by omega
  rw [hs]
  have h1 : (q + 1) * (t * (t + 1) * y) ≥ (q + 1) * (t * (t + 1) * (3 * q + 2)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hy2)
  nlinarith [h1, Nat.mul_le_mul ht ht, Nat.mul_le_mul hq ht]

/-- **Theorem R for the hexagon**: regular, balanced. -/
theorem theoremR (hc : ¬ IsSquare (-c)) (hG : GoodCubic c c0 c1) (hm2 : 2 ≤ m) :
    ∃ G : SimpleGraph (Fin (2 * Fintype.card (VL c c0 c1 m))),
      IsBipartiteRegDiam G (Fintype.card F + m) 6 := by
  have hm : 0 < m := by omega
  obtain ⟨S, hSP, hSc, hSq⟩ := exists_deletion hc hG hm
  have hlev := hex_levelled_bound hc hG hm
  have hbi : IsBipartiteDegDiam (biGraph (rr c c0 c1 m)) (Fintype.card F + 1 + (m - 1)) 6 :=
    isBipartiteDegDiam_biGraph_rel hlev
  have hdegL : ∀ a, degL (rr c c0 c1 m) a ≤ Fintype.card F + m := fun a => by
    have := hbi.2.1 (Sum.inl a)
    rw [BipartiteDD.Regular.ncard_neighborSet_inl] at this
    unfold degL
    omega
  have hdegR : ∀ b, degR (rr c c0 c1 m) b ≤ Fintype.card F + m := fun b => by
    have := hbi.2.1 (Sum.inr b)
    rw [BipartiteDD.Regular.ncard_neighborSet_inr] at this
    unfold degR
    omega
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hSset : ∀ b ∈ (S : Set (VR c c0 c1 m)), isP c c0 c1 hm b := fun b hb => hSP b (by simpa using hb)
  refine regular_of_twins (rr c c0 c1 m) (Fintype.card F + m) (m - 1) 6 S hSc ?_ hdegL hdegR ?_ ?_ ?_
    hbi.2.2
  · intro b hb
    obtain ⟨b', hb'1, hb'2⟩ := twin_of_isP hc hm (hSset b hb)
    exact ⟨b', fun h => hb'1 (hSset b' h), hb'2⟩
  · intro a
    have := degL_ge hc hm (S : Set (VR c c0 c1 m)) hSset a
    omega
  · intro b
    have := degR_ge hm b.1
    show Fintype.card F + m - degR (rr c c0 c1 m) b.1 ≤ m - 1
    omega
  · -- the total deficit
    have hdel : ∀ a, (S.filter fun b => rr c c0 c1 m a b).card ≤
        Fintype.card F + m - degL (restrictR (rr c c0 c1 m) (S : Set (VR c c0 c1 m))) a := fun a => by
      have := degL_restrictR_add (rr c c0 c1 m) S a
      have := hdegL a
      omega
    have hsum : ∑ a, (S.filter fun b => rr c c0 c1 m a b).card ≤
        ∑ a, (Fintype.card F + m - degL (restrictR (rr c c0 c1 m) (S : Set (VR c c0 c1 m))) a) :=
      Finset.sum_le_sum (fun a _ => hdel a)
    have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := (Finset.univ : Finset (VL c c0 c1 m))) (t := S) (rr c c0 c1 m)
    simp only [Finset.bipartiteAbove, Finset.bipartiteBelow, Finset.mem_univ, true_and] at hdc
    have hge : ∀ b ∈ S, Fintype.card F + 1 ≤ (Finset.univ.filter fun a => rr c c0 c1 m a b).card := by
      intro b _
      have := degR_ge hm b
      unfold degR at this
      rwa [ncard_setOf_eq_card_filter] at this
    have hT : S.card * (Fintype.card F + 1) ≤ ∑ a, (S.filter fun b => rr c c0 c1 m a b).card := by
      rw [hdc]
      calc S.card * (Fintype.card F + 1) = ∑ b ∈ S, (Fintype.card F + 1) := by simp
        _ ≤ _ := Finset.sum_le_sum hge
    have hbig := hbig_arith (Fintype.card F) m S.card hq2 hm2 hSq
    calc 2 * (m - 1) * (Fintype.card F + m + (m - 1) + 1) < (Fintype.card F + 1) * S.card := hbig
      _ = S.card * (Fintype.card F + 1) := by ring
      _ ≤ _ := hT.trans hsum

end BipartiteDD.HexagonD
