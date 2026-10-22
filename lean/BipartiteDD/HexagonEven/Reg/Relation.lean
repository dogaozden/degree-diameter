import BipartiteDD.HexagonEven.ThmD
import BipartiteDD.Regular.Defs

/-! Theorem R instance, part 1: the doubled and whiskered graph of `theoremD` as an explicit bipartite relation.

With `ht d v W x` the height of a point or line `x` in the levels `lev d v W` (`Doubling.height`), the versions of a
point `p` are the strings `Fin (ht (inl p)) → Fin m` and those of a line `l` the strings `Fin (ht (inr l)) → Fin m`
(`PtVer`, `LnVer`). `levRel d v W m a b` says that the version `a` of a point is adjacent to the version `b` of a
line in Delorme's levelled doubling (`Doubling.levelled`). Then `biGraph (levRel d v W m)` is that graph, with the
points on the left: `levRel_isBipartiteDegDiam` gives its degree and diameter bounds, and `card_ptVer`,
`card_lnVer` its two side sizes. -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonEven

open BipartiteDD.HexagonD

open BipartiteDD.Hexagon BipartiteDD.Doubling BipartiteDD.Regular Module Submodule
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] {d : F}

local notation "GH" => Hexagon.incGraph (hexInc (F := F))

/-- Every vertex of `SPt F ⊕ HLine F` is outside the level `A₃ = ∅`. -/
theorem exists_notMem_lev (d : F) (v : HLine F) (W : Set (HLine F)) (x : SPt F ⊕ HLine F) :
    ∃ i, x ∉ lev d v W i :=
  ⟨3, by rw [lev_three]; exact Set.notMem_empty x⟩

/-- The height of a point or line: the number of levels `lev d v W` containing it. -/
noncomputable def ht (d : F) (v : HLine F) (W : Set (HLine F)) (x : SPt F ⊕ HLine F) : ℕ :=
  height (lev d v W) (exists_notMem_lev d v W) x

/-- The versions of the points: `p` with a string of length `ht (inl p)` over `m` letters. -/
abbrev PtVer (d : F) (v : HLine F) (W : Set (HLine F)) (m : ℕ) : Type _ :=
  Σ p : SPt F, Fin (ht d v W (Sum.inl p)) → Fin m

/-- The versions of the lines: `l` with a string of length `ht (inr l)` over `m` letters. -/
abbrev LnVer (d : F) (v : HLine F) (W : Set (HLine F)) (m : ℕ) : Type _ :=
  Σ l : HLine F, Fin (ht d v W (Sum.inr l)) → Fin m

/-- A point version is adjacent to a line version when they are adjacent in the levelled doubling. -/
def levRel (d : F) (v : HLine F) (W : Set (HLine F)) (m : ℕ) (a : PtVer d v W m) (b : LnVer d v W m) :
    Prop :=
  (levelled GH m (ht d v W)).Adj ⟨Sum.inl a.1, a.2⟩ ⟨Sum.inr b.1, b.2⟩

/-- The versions of the levelled doubling split into the versions of points and of lines. -/
def verEquiv (d : F) (v : HLine F) (W : Set (HLine F)) (m : ℕ) :
    Ver (SPt F ⊕ HLine F) m (ht d v W) ≃ PtVer d v W m ⊕ LnVer d v W m where
  toFun x := match x with
    | ⟨Sum.inl p, s⟩ => Sum.inl ⟨p, s⟩
    | ⟨Sum.inr l, s⟩ => Sum.inr ⟨l, s⟩
  invFun y := match y with
    | Sum.inl ⟨p, s⟩ => ⟨Sum.inl p, s⟩
    | Sum.inr ⟨l, s⟩ => ⟨Sum.inr l, s⟩
  left_inv x := by
    rcases x with ⟨_ | _, _⟩ <;> rfl
  right_inv y := by
    rcases y with ⟨_, _⟩ | ⟨_, _⟩ <;> rfl

/-- The bipartite graph of `levRel` is the levelled doubling, read through `verEquiv`. -/
theorem comap_levelled_eq (d : F) (v : HLine F) (W : Set (HLine F)) (m : ℕ) :
    (levelled GH m (ht d v W)).comap (verEquiv d v W m).symm = biGraph (levRel d v W m) := by
  ext u w
  rcases u with ⟨p, s⟩ | ⟨l, t⟩ <;> rcases w with ⟨p', s'⟩ | ⟨l', t'⟩
  · refine ⟨fun h => ?_, fun h => (biGraph_adj_inl_inl _ _ _ h).elim⟩
    have h1 : (GH).Adj (Sum.inl p) (Sum.inl p') := h.1
    exact (Hexagon.incGraph_not_adj_inl_inl h1).elim
  · exact Iff.rfl
  · exact ⟨fun h => SimpleGraph.adj_symm (levelled GH m (ht d v W)) h, fun h => SimpleGraph.adj_symm (levelled GH m (ht d v W)) h⟩
  · refine ⟨fun h => ?_, fun h => (biGraph_adj_inr_inr _ _ _ h).elim⟩
    have h1 : (GH).Adj (Sum.inr l) (Sum.inr l') := h.1
    exact (Hexagon.incGraph_not_adj_inr_inr h1).elim

/-- Lines and points of the levels: `i < ht x` iff `x` lies in the level `i`. -/
theorem lt_ht_iff (v : SLineE d) (W : Set (HLine F)) (x : SPt F ⊕ HLine F) (i : ℕ) :
    i < ht d v.1 W x ↔ x ∈ lev d v.1 W i :=
  lt_height_iff (lev_antitone v.1 v.2 W)

/-- The levelled doubling of the hexagon, with the whiskers `W`, has maximum degree `q + m` and diameter `≤ 6`. -/
theorem levelled_isBipartiteDegDiam (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (hchar : (2 : F) = 0) {m : ℕ} (hm : 0 < m) (v : SLineE d)
    {W : Set (HLine F)} (hW : Whiskers d v W) :
    IsBipartiteDegDiam (levelled GH m (ht d v.1 W)) (Fintype.card F + m) 6 := by
  have : Fintype (SPt F ⊕ HLine F) := Fintype.ofFinite _
  have hA := lev_antitone (d := d) v.1 v.2 W
  have hG : IsBipartiteDegDiam GH (Fintype.card F + 1) 6 :=
    ⟨genPolygonGraph_hexagon_even.colorable, by
      rintro (p | l)
      · rw [ncard_neighborSet_inl]
      · rw [ncard_neighborSet_inr], genPolygonGraph_hexagon_even.ediam.le⟩
  have hc6 : CondC GH (lev d v.1 W 0) 6 :=
    genPolygonGraph_hexagon_even.condC_of_forestDiam (forestDiam_pi hd hchar (A := lev d v.1 W 0)
      (fun p => by simp [lev, A0]) (fun l hl => by simp [lev, A0, hl]))
  have hmain := isBipartiteDegDiam_levelled (G := GH) (Δ := Fintype.card F + 1) (D := 6) hm hG hA
    (K := 3) (lev_three v.1 W) (lev_ha1 hd hchar) (lev_ha2 hd hchar) (lev_hb hd hchar hW) hc6
  rw [show Fintype.card F + m = Fintype.card F + 1 + (m - 1) by omega]
  exact hmain

section Counts

variable [Fintype (SPt F)] [Fintype (HLine F)]

theorem card_ptVer (d : F) (v : HLine F) (W : Set (HLine F)) (m : ℕ) :
    Fintype.card (PtVer d v W m) = ∑ p : SPt F, m ^ ht d v W (Sum.inl p) := by
  simp [PtVer, Fintype.card_sigma]

theorem card_lnVer (d : F) (v : HLine F) (W : Set (HLine F)) (m : ℕ) :
    Fintype.card (LnVer d v W m) = ∑ l : HLine F, m ^ ht d v W (Sum.inr l) := by
  simp [LnVer, Fintype.card_sigma]

/-- The number of points of height above `i` is the number of points in the level `i`. -/
theorem card_filter_ptHeight (v : SLineE d) (W : Set (HLine F)) (i : ℕ) :
    (Finset.univ.filter fun p : SPt F => i < ht d v.1 W (Sum.inl p)).card =
      {p : SPt F | Sum.inl p ∈ lev d v.1 W i}.ncard := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext p
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  exact lt_ht_iff v W (Sum.inl p) i

/-- The number of lines of height above `i` is the number of lines in the level `i`. -/
theorem card_filter_lnHeight (v : SLineE d) (W : Set (HLine F)) (i : ℕ) :
    (Finset.univ.filter fun l : HLine F => i < ht d v.1 W (Sum.inr l)).card =
      {l : HLine F | Sum.inr l ∈ lev d v.1 W i}.ncard := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext l
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  exact lt_ht_iff v W (Sum.inr l) i

theorem sum_ptVer (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (hchar : (2 : F) = 0) (v : SLineE d) (W : Set (HLine F)) {m : ℕ} (hm : 0 < m) :
    ∑ p : SPt F, m ^ ht d v.1 W (Sum.inl p) = Fintype.card (SPt F) +
      (m - 1) * ((Fintype.card F ^ 3 + 1) * (Fintype.card F + 1) + m * (Fintype.card F + 1)) := by
  have hK : ∀ p : SPt F, ht d v.1 W (Sum.inl p) ≤ 3 := fun p =>
    height_le (A := lev d v.1 W) (by rw [lev_three]; exact Set.notMem_empty _)
  have key := sum_pow_height (V := SPt F) (h := fun p => ht d v.1 W (Sum.inl p)) (K := 3) hm hK
  rw [key]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, card_filter_ptHeight]
  have h0 : {p : SPt F | Sum.inl p ∈ lev d v.1 W 0} = {p : SPt F | OnPiE d p} := by
    ext p
    simp [lev, A0]
  have h1 : {p : SPt F | Sum.inl p ∈ lev d v.1 W 1} = {p : SPt F | hexInc p v.1} := by
    ext p
    simp [lev, A1]
  have h2 : {p : SPt F | Sum.inl p ∈ lev d v.1 W 2} = ∅ := by
    ext p
    simp [lev, A2]
  rw [h0, h1, h2, ncard_onPiE hd hchar, ncard_hexInc_points]
  simp

theorem sum_lnVer (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (hchar : (2 : F) = 0) (v : SLineE d) {W : Set (HLine F)} (hW : Whiskers d v W) {m : ℕ}
    (hm : 0 < m) :
    ∑ l : HLine F, m ^ ht d v.1 W (Sum.inr l) = Fintype.card (HLine F) +
      (m - 1) * ((Fintype.card F ^ 3 + 1) + Fintype.card F * (Fintype.card F + 1) + W.ncard +
        m * (Fintype.card F ^ 3 + 1) + m ^ 2) := by
  have hK : ∀ l : HLine F, ht d v.1 W (Sum.inr l) ≤ 3 := fun l =>
    height_le (A := lev d v.1 W) (by rw [lev_three]; exact Set.notMem_empty _)
  have key := sum_pow_height (V := HLine F) (h := fun l => ht d v.1 W (Sum.inr l)) (K := 3) hm hK
  rw [key]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, card_filter_lnHeight]
  have h0 : {l : HLine F | Sum.inr l ∈ lev d v.1 W 0} = {l : HLine F | InPiE d l ∨ Meets v.1 l ∨ l ∈ W} := by
    ext l
    simp [lev, A0]
  have h1 : {l : HLine F | Sum.inr l ∈ lev d v.1 W 1} = {l : HLine F | InPiE d l} := by
    ext l
    simp [lev, A1]
  have h2 : {l : HLine F | Sum.inr l ∈ lev d v.1 W 2} = {v.1} := by
    ext l
    simp [lev, A2]
  rw [h0, h1, h2, ncard_L0 hd hchar v hW, ncard_slineE hd hchar, Set.ncard_singleton]
  simp

end Counts

/-- The levelled doubling, read as the bipartite graph of `levRel`: maximum degree `q + m`, diameter `≤ 6`. -/
theorem levRel_isBipartiteDegDiam (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (hchar : (2 : F) = 0) {m : ℕ} (hm : 0 < m) (v : SLineE d)
    {W : Set (HLine F)} (hW : Whiskers d v W) :
    IsBipartiteDegDiam (biGraph (levRel d v.1 W m)) (Fintype.card F + m) 6 := by
  rw [← comap_levelled_eq]
  exact isBipartiteDegDiam_comap (verEquiv d v.1 W m) (levelled_isBipartiteDegDiam hd hchar hm v hW)

section Final

/-- The two side sizes, for any `W` with `|W| = q⁴ - q²`: the points and lines of the doubled graph differ by
`(m - 1) m (q³ - q + m)` (written here as `|β| + (m - 1) m q = |α| + (m - 1) m (q³ + m)`). -/
theorem natCard_sides (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (hchar : (2 : F) = 0) {m : ℕ} (hm : 0 < m) (v : SLineE d) {W : Set (HLine F)}
    (hW : Whiskers d v W) (hWc : W.ncard + Fintype.card F ^ 2 = Fintype.card F ^ 4) :
    Nat.card (PtVer d v.1 W m) = (Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4) +
        (m - 1) * ((Fintype.card F ^ 3 + 1) * (Fintype.card F + 1) + m * (Fintype.card F + 1)) ∧
    Nat.card (LnVer d v.1 W m) + (m - 1) * m * Fintype.card F =
        Nat.card (PtVer d v.1 W m) + (m - 1) * m * (Fintype.card F ^ 3 + m) := by
  have : Fintype (SPt F) := Fintype.ofFinite _
  have : Fintype (HLine F) := by
    have := finite_hline_even (F := F)
    exact Fintype.ofFinite _
  have hS : Fintype.card (SPt F) = (Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4) := by
    rw [← Nat.card_eq_fintype_card, card_spt_eq]
  have hL : Fintype.card (HLine F) = (Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4) := by
    rw [← Nat.card_eq_fintype_card, card_hline_even, ← card_spt_div, card_spt_eq]
  simp only [Nat.card_eq_fintype_card]
  refine ⟨?_, ?_⟩
  · rw [card_ptVer, sum_ptVer hd hchar v _ hm, hS]
  · rw [card_ptVer, card_lnVer, sum_ptVer hd hchar v _ hm, sum_lnVer hd hchar v hW hm, hS, hL]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hW' : (W.ncard : ℤ) + (Fintype.card F : ℤ) ^ 2 = (Fintype.card F : ℤ) ^ 4 := by exact_mod_cast hWc
    zify
    linear_combination (k : ℤ) * hW'

end Final

/-- **Brief step 1 (`theoremD` as a relation).** For `q` odd and `m ≥ 1` there are a line `v` of the spread and
a set `W` of whiskers with `|W| = q⁴ - q²` such that the bipartite graph of `levRel` has maximum degree `q + m`,
diameter `≤ 6`, and its two sides satisfy `natCard_sides`. -/
theorem exists_levRel {m : ℕ} (hm : 0 < m) (hchar : (2 : F) = 0) (hq : 4 ≤ Fintype.card F) :
    ∃ (d : F) (v : SLineE d) (W : Set (HLine F)),
      IsBipartiteDegDiam (biGraph (levRel d v.1 W m)) (Fintype.card F + m) 6 ∧
      Nat.card (PtVer d v.1 W m) = (Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4) +
        (m - 1) * ((Fintype.card F ^ 3 + 1) * (Fintype.card F + 1) + m * (Fintype.card F + 1)) ∧
      Nat.card (LnVer d v.1 W m) + (m - 1) * m * Fintype.card F =
        Nat.card (PtVer d v.1 W m) + (m - 1) * m * (Fintype.card F ^ 3 + m) := by
  obtain ⟨d, c0, c1, hd, hG, hW, hcard, -⟩ := theorem4_even (F := F) hchar hq
  exact ⟨d, vS' d, Wset d c0 c1, levRel_isBipartiteDegDiam hd hchar hm (vS' d) hW,
    (natCard_sides hd hchar hm (vS' d) hW hcard).1, (natCard_sides hd hchar hm (vS' d) hW hcard).2⟩

end BipartiteDD.HexagonEven
