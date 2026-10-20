import BipartiteDD.HexagonD.LevelsCount

/-! Theorem D, slice 2, parts 10-11 (targets 2 and 3): Delorme's levelled doubling of `H(q)`, with whiskers.

`exists_levelled_hexagon`: for `F` a finite field of odd characteristic with `q = |F|`, `m ≥ 1`, a line `v` of
the Hermitian spread and a set `W` of whiskers (lines opposite `v`, not in `S`, with no free point on two of
them), there is a bipartite graph of maximum degree at most `q + m`, diameter at most `6`, and
`2 (q + 1)(q⁴ + q² + 1) + (m - 1)(q⁴ + 2q³ + q² + 2q + 2 + |W| + m (q³ + q + 2) + m²)` vertices.

For `W = ∅` and `m = 2` this is Delorme's 1985 bound (`delorme_bound_hexagon`)
`n_b(q + 2, 6) ≥ 2(q + 1)(q⁴ + q² + 1) + q⁴ + 4q³ + q² + 4q + 10`;
each whisker adds `m - 1` vertices (`whiskers_bound_hexagon`). -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon BipartiteDD.Doubling Module Submodule
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)] {c : F}

local notation "GH" => Hexagon.incGraph (hexInc (F := F))

theorem ncard_neighborSet_inl (p : SPt F) : ((GH).neighborSet (Sum.inl p)).ncard = Fintype.card F + 1 := by
  have : (GH).neighborSet (Sum.inl p) = Sum.inr '' {l : HLine F | hexInc p l} := by
    ext (x | l)
    · simp
    · simp [Hexagon.incGraph_adj_inl_inr]
  rw [this, Set.ncard_image_of_injective _ Sum.inr_injective, ncard_hexInc_lines]

theorem ncard_neighborSet_inr (l : HLine F) : ((GH).neighborSet (Sum.inr l)).ncard = Fintype.card F + 1 := by
  have : (GH).neighborSet (Sum.inr l) = Sum.inl '' {p : SPt F | hexInc p l} := by
    ext (p | x)
    · simp [Hexagon.incGraph_adj_inr_inl]
    · simp
  rw [this, Set.ncard_image_of_injective _ Sum.inl_injective, ncard_hexInc_points]

theorem card_vertices : Nat.card (SPt F ⊕ HLine F) =
    2 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) := by
  rw [Nat.card_sum, card_hline, card_spt_div, ← card_spt_div]
  rw [card_spt_eq]
  ring

theorem ncard_L0 (hc : ¬ IsSquare (-c)) (v : SLine c) {W : Set (HLine F)} (hW : Whiskers c v W) :
    {l : HLine F | InPi c l ∨ Meets v.1 l ∨ l ∈ W}.ncard =
      (Fintype.card F ^ 3 + 1) + Fintype.card F * (Fintype.card F + 1) + W.ncard := by
  have hset : {l : HLine F | InPi c l ∨ Meets v.1 l ∨ l ∈ W} =
      {l | InPi c l} ∪ ({l | Meets v.1 l ∧ ¬ InPi c l} ∪ W) := by
    ext l
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    by_cases h : InPi c l <;> tauto
  rw [hset, Set.ncard_union_eq, Set.ncard_union_eq, ncard_sline hc, ncard_meets hc v]
  · ring
  · rw [Set.disjoint_left]
    rintro l ⟨hl1, hl2⟩ hlW
    exact hW.not_meets hlW hl1
  · rw [Set.disjoint_left]
    rintro l hl (⟨-, h⟩ | h)
    · exact h hl
    · exact hW.not_inPi l h hl

/-- **Delorme's levelled doubling of `H(q)` with whiskers** (targets 2 and 3). -/
theorem exists_levelled_hexagon (hc : ¬ IsSquare (-c)) {m : ℕ} (hm : 0 < m) (v : SLine c)
    {W : Set (HLine F)} (hW : Whiskers c v W) :
    ∃ H : SimpleGraph (Fin (2 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) +
        (m - 1) * ((Fintype.card F ^ 4 + 2 * Fintype.card F ^ 3 + Fintype.card F ^ 2 +
          2 * Fintype.card F + 2 + W.ncard) + m * (Fintype.card F ^ 3 + Fintype.card F + 2) + m ^ 2))),
      IsBipartiteDegDiam H (Fintype.card F + m) 6 := by
  have : Fintype (SPt F ⊕ HLine F) := Fintype.ofFinite _
  have hA := lev_antitone (c := c) v.1 v.2 W
  obtain ⟨H, hH⟩ := delorme_levelled_polygon (G := GH) (n := 6) (Δ := Fintype.card F + 1) (m := m)
    (A := lev c v.1 W) hm genPolygonGraph_hexagon
    (by
      rintro (p | l)
      · rw [ncard_neighborSet_inl]
      · rw [ncard_neighborSet_inr])
    hA (K := 3) (lev_three v.1 W) (lev_ha1 hc) (lev_ha2 hc) (lev_hb hc hW)
    (forestDiam_pi hc (A := lev c v.1 W 0) (fun p => by simp [lev, A0]) (fun l hl => by
      simp [lev, A0, hl]))
  have key : Nat.card (SPt F ⊕ HLine F) + (m - 1) * ∑ i ∈ Finset.range 3, m ^ i * (lev c v.1 W i).ncard =
      2 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) +
        (m - 1) * ((Fintype.card F ^ 4 + 2 * Fintype.card F ^ 3 + Fintype.card F ^ 2 +
          2 * Fintype.card F + 2 + W.ncard) + m * (Fintype.card F ^ 3 + Fintype.card F + 2) + m ^ 2) := by
    have h0 : (lev c v.1 W 0).ncard = (Fintype.card F ^ 3 + 1) * (Fintype.card F + 1) +
        ((Fintype.card F ^ 3 + 1) + Fintype.card F * (Fintype.card F + 1) + W.ncard) := by
      show (A0 c v.1 W).ncard = _
      rw [A0, ncard_sumSet, ncard_onPi hc, ncard_L0 hc v hW]
    have h1 : (lev c v.1 W 1).ncard = (Fintype.card F + 1) + (Fintype.card F ^ 3 + 1) := by
      show (A1 c v.1).ncard = _
      rw [A1, ncard_sumSet, ncard_hexInc_points, ncard_sline hc]
    have h2 : (lev c v.1 W 2).ncard = 1 := by
      show (A2 v.1).ncard = _
      simp [A2]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, card_vertices]
    ring_nf
  have main : ∃ H : SimpleGraph (Fin (Nat.card (SPt F ⊕ HLine F) +
      (m - 1) * ∑ i ∈ Finset.range 3, m ^ i * (lev c v.1 W i).ncard)),
      IsBipartiteDegDiam H (Fintype.card F + m) 6 := by
    refine ⟨H, ?_⟩
    rw [show Fintype.card F + m = Fintype.card F + 1 + (m - 1) by omega]
    exact hH
  rw [key] at main
  exact main

/-- There is `c` with `-c` a non-square. -/
theorem exists_nonsquare_neg : ∃ c : F, ¬ IsSquare (-c) := by
  have hchar : ringChar F ≠ 2 := by
    intro h
    have : ((2 : ℕ) : F) = 0 := by
      have : CharP F 2 := h ▸ ringChar.charP F
      exact CharP.cast_eq_zero F 2
    exact NeZero.ne (2 : F) (by exact_mod_cast this)
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
  exact ⟨-a, by simpa using ha⟩

/-- A spread line exists. -/
theorem nonempty_sline (hc : ¬ IsSquare (-c)) : Nonempty (SLine c) := by
  classical
  have := card_sline (c := c) hc
  exact Fintype.card_pos_iff.1 (by rw [this]; omega)

theorem Whiskers.empty (v : SLine c) : Whiskers c v (∅ : Set (HLine F)) :=
  ⟨by simp, by simp, by simp⟩

/-- **Delorme's bound for the hexagon** (target 2, `m`-ary): for every finite field `F` of odd
characteristic (`q = |F|`) and `m ≥ 1` there is a bipartite graph of maximum degree `≤ q + m` and diameter
`≤ 6` with `2(q+1)(q⁴+q²+1) + (m-1)(q⁴+2q³+q²+2q+2 + m(q³+q+2) + m²)` vertices. -/
theorem delorme_bound_hexagon {m : ℕ} (hm : 0 < m) :
    ∃ H : SimpleGraph (Fin (2 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) +
        (m - 1) * ((Fintype.card F ^ 4 + 2 * Fintype.card F ^ 3 + Fintype.card F ^ 2 +
          2 * Fintype.card F + 2) + m * (Fintype.card F ^ 3 + Fintype.card F + 2) + m ^ 2))),
      IsBipartiteDegDiam H (Fintype.card F + m) 6 := by
  obtain ⟨c, hc⟩ := exists_nonsquare_neg (F := F)
  obtain ⟨v⟩ := nonempty_sline hc
  have := exists_levelled_hexagon hc hm v (Whiskers.empty v)
  rw [Set.ncard_empty, add_zero] at this
  exact this

/-- **Delorme's 1985 bound** `n_b(q+2, 6) ≥ 2(q+1)(q⁴+q²+1) + q⁴+4q³+q²+4q+10` for odd `q`. -/
theorem delorme_bound_hexagon_two :
    ∃ H : SimpleGraph (Fin (2 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) +
        (Fintype.card F ^ 4 + 4 * Fintype.card F ^ 3 + Fintype.card F ^ 2 + 4 * Fintype.card F + 10))),
      IsBipartiteDegDiam H (Fintype.card F + 2) 6 := by
  have := delorme_bound_hexagon (F := F) (m := 2) (by norm_num)
  have e : 2 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) +
        (2 - 1) * ((Fintype.card F ^ 4 + 2 * Fintype.card F ^ 3 + Fintype.card F ^ 2 +
          2 * Fintype.card F + 2) + 2 * (Fintype.card F ^ 3 + Fintype.card F + 2) + 2 ^ 2) =
      2 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) +
        (Fintype.card F ^ 4 + 4 * Fintype.card F ^ 3 + Fintype.card F ^ 2 + 4 * Fintype.card F + 10) := by
    norm_num; ring
  rw [e] at this
  exact this

/-- **Theorem 3 (whiskers)**: any set `W` of whiskers adds `(m - 1) |W|` vertices to Delorme's bound. -/
theorem whiskers_bound_hexagon (hc : ¬ IsSquare (-c)) {m : ℕ} (hm : 0 < m) (v : SLine c)
    {W : Set (HLine F)} (hW : Whiskers c v W) :
    ∃ H : SimpleGraph (Fin (2 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) +
        (m - 1) * ((Fintype.card F ^ 4 + 2 * Fintype.card F ^ 3 + Fintype.card F ^ 2 +
          2 * Fintype.card F + 2) + m * (Fintype.card F ^ 3 + Fintype.card F + 2) + m ^ 2) +
        (m - 1) * W.ncard)),
      IsBipartiteDegDiam H (Fintype.card F + m) 6 := by
  have := exists_levelled_hexagon hc hm v hW
  have e : 2 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) +
        (m - 1) * ((Fintype.card F ^ 4 + 2 * Fintype.card F ^ 3 + Fintype.card F ^ 2 +
          2 * Fintype.card F + 2 + W.ncard) + m * (Fintype.card F ^ 3 + Fintype.card F + 2) + m ^ 2) =
      2 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) +
        (m - 1) * ((Fintype.card F ^ 4 + 2 * Fintype.card F ^ 3 + Fintype.card F ^ 2 +
          2 * Fintype.card F + 2) + m * (Fintype.card F ^ 3 + Fintype.card F + 2) + m ^ 2) +
        (m - 1) * W.ncard := by ring
  rw [e] at this
  exact this

/-- The whisker hypotheses in the form of the report: lines of `W` are not in `S`, are opposite `v` (at
distance `6`), and no free point (off `Π`, at distance `5` from `v`) is on two of them. -/
theorem Whiskers.of_edist (v : SLine c) {W : Set (HLine F)} (h1 : ∀ w ∈ W, ¬ InPi c w)
    (h2 : ∀ w ∈ W, (GH).edist (Sum.inr v.1) (Sum.inr w) = 6)
    (h3 : ∀ p : SPt F, ¬ OnPi c p → (GH).edist (Sum.inl p) (Sum.inr v.1) = 5 →
      ∀ w ∈ W, ∀ w' ∈ W, hexInc p w → hexInc p w' → w = w') : Whiskers c v W where
  not_inPi := h1
  opp w hw := opp_of_edist_eq_six (h2 w hw)
  free p hp hM w hw w' hw' hpw hpw' := by
    refine h3 p hp (edist_eq_five genPolygonGraph_hexagon (fun h => hp (onPi_of_mem (s := v) h)) ?_)
      w hw w' hw' hpw hpw'
    rintro ⟨M, r, hpM, hrM, hrv⟩
    exact hM ⟨M, hpM, r, hrv, hrM⟩

end BipartiteDD.HexagonD
