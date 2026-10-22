import BipartiteDD.HexagonEven.ExactW
import BipartiteDD.HexagonEven.Delorme
import BipartiteDD.HexagonD.WCount

/-! Theorem D (even `q`), counting and the final bound (mirror of `HexagonD/WCount.lean` and `HexagonD/TheoremD.lean`).

* `ncard_offPiE`: a line not in `Π` has `q` points off `Π`;
* `ncard_notFreeE`, `ncard_freeE`: the free points number `q³(q² - 1)`;
* `ncard_wsetE`: `|Wset| = q⁴ - q²` (each free point lies on exactly one whisker line, each whisker line has `q`
  free points);
* `wset_whiskers_even`: `Wset` is a set of whiskers for `v`;
* `theoremD_even`: the bound of Theorem D for every even `q ≥ 4`. -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonEven

open BipartiteDD.Hexagon BipartiteDD.HexagonD Module Submodule
open scoped Classical

variable {F : Type*} [Field F]

theorem ncard_offPiE [Fintype F] {d : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (hchar : (2 : F) = 0)
    {l : HLine F} (hl : ¬ InPiE d l) :
    {p : SPt F | hexInc p l ∧ ¬ OnPiE d p}.ncard = Fintype.card F := by
  have h1 : {p : SPt F | hexInc p l ∧ OnPiE d p}.ncard = 1 := by
    rw [Set.ncard_eq_one]
    obtain ⟨p, hp, hpl⟩ := exists_piPt d l
    refine ⟨p, ?_⟩
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hq, hqPi⟩
      exact eq_of_onPi_of_not_inPi hqPi hp hq hpl hl
    · rintro rfl
      exact ⟨hpl, hp⟩
  have h2 : {p : SPt F | hexInc p l}.ncard = Fintype.card F + 1 := ncard_hexInc_points l
  have hu : {p : SPt F | hexInc p l} =
      {p : SPt F | hexInc p l ∧ OnPiE d p} ∪ {p : SPt F | hexInc p l ∧ ¬ OnPiE d p} := by
    ext p; simp only [Set.mem_setOf_eq, Set.mem_union]; tauto
  have hdis : Disjoint {p : SPt F | hexInc p l ∧ OnPiE d p}
      {p : SPt F | hexInc p l ∧ ¬ OnPiE d p} := by
    rw [Set.disjoint_left]
    rintro p ⟨-, h1⟩ ⟨-, h2⟩
    exact h2 h1
  rw [hu, Set.ncard_union_eq hdis, h1] at h2
  omega

/-- The points off `Π` collinear with `v`. -/
def NotFreeE (d : F) : Set (SPt F) :=
  {p | ¬ OnPiE d p ∧ ∃ M : HLine F, hexInc p M ∧ Meets vStd' M}

/-- The free points. -/
def FreePtsE (d : F) : Set (SPt F) :=
  {p | ¬ OnPiE d p ∧ ¬ ∃ M : HLine F, hexInc p M ∧ Meets vStd' M}

theorem ncard_notFreeE [Fintype F] {d : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (hchar : (2 : F) = 0) :
    (NotFreeE d).ncard = Fintype.card F ^ 2 * (Fintype.card F + 1) := by
  have hpv : ∀ p : SPt F, ¬ OnPiE d p → ¬ hexInc p (vStd' : HLine F) := fun p hp h =>
    hp (vStd'_Pi d _ h)
  let g : SPt F → HLine F := fun p =>
    if h : ∃ M : HLine F, hexInc p M ∧ Meets (vStd' : HLine F) M then h.choose else vStd'
  have hg : ∀ p ∈ NotFreeE d, hexInc p (g p) ∧ Meets (vStd' : HLine F) (g p) := by
    intro p hp
    have h := hp.2
    simp only [g, dif_pos h]
    exact h.choose_spec
  have hT : ∀ p ∈ NotFreeE d, g p ∈ {M : HLine F | Meets (vStd' : HLine F) M ∧ ¬ InPiE d M} := by
    intro p hp
    obtain ⟨h1, h2⟩ := hg p hp
    refine ⟨h2, fun hi => hp.1 (hi _ h1)⟩
  have := ncard_fiberwise (NotFreeE d) {M : HLine F | Meets (vStd' : HLine F) M ∧ ¬ InPiE d M} g hT
    (Fintype.card F) (by
      rintro M ⟨hM1, hM2⟩
      have : {a | a ∈ NotFreeE d ∧ g a = M} = {p : SPt F | hexInc p M ∧ ¬ OnPiE d p} := by
        ext p
        simp only [Set.mem_setOf_eq]
        constructor
        · rintro ⟨hp, rfl⟩
          exact ⟨(hg p hp).1, hp.1⟩
        · rintro ⟨hpM, hpPi⟩
          have hp : p ∈ NotFreeE d := ⟨hpPi, M, hpM, hM1⟩
          refine ⟨hp, ?_⟩
          obtain ⟨h1, ⟨r, hr, hr'⟩⟩ := hg p hp
          obtain ⟨r', hr'v, hr'M⟩ := hM1
          exact eq_of_triangle genPolygonGraph_hexagon_even (hpv p hpPi) h1 hr' hr hpM hr'M hr'v
      rw [this]
      exact ncard_offPiE hd hchar hM2)
  rw [this]
  have hm := ncard_meets hd hchar (vS' d)
  have hm' : {M : HLine F | Meets (vStd' : HLine F) M ∧ ¬ InPiE d M}.ncard =
      Fintype.card F * (Fintype.card F + 1) := hm
  rw [hm']
  ring

theorem ncard_freeE [Fintype F] {d : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (hchar : (2 : F) = 0) :
    (FreePtsE d).ncard + Fintype.card F ^ 2 * (Fintype.card F + 1) +
      (Fintype.card F ^ 3 + 1) * (Fintype.card F + 1) =
      (Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4) := by
  have hu : (Set.univ : Set (SPt F)) = {p | OnPiE d p} ∪ NotFreeE d ∪ FreePtsE d := by
    ext p
    simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq, NotFreeE, FreePtsE, true_iff]
    by_cases h1 : OnPiE d p <;> by_cases h2 : ∃ M : HLine F, hexInc p M ∧ Meets (vStd' : HLine F) M <;>
      simp [h1, h2]
  have hd1 : Disjoint {p : SPt F | OnPiE d p} (NotFreeE d) := by
    rw [Set.disjoint_left]; rintro p h1 ⟨h2, -⟩; exact h2 h1
  have hd2 : Disjoint ({p : SPt F | OnPiE d p} ∪ NotFreeE d) (FreePtsE d) := by
    rw [Set.disjoint_left]
    rintro p (h1 | ⟨h1, h2⟩) ⟨h3, h4⟩
    · exact h3 h1
    · exact h4 h2
  have := congrArg Set.ncard hu
  rw [Set.ncard_univ, Set.ncard_union_eq hd2, Set.ncard_union_eq hd1, ncard_onPiE hd hchar,
    ncard_notFreeE hd hchar, card_spt_eq] at this
  omega

/-- `Wset` is a set of whiskers for the spread line `v`. -/
theorem wset_whiskers_even [Fintype F] {d c0 c1 : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0)
    (hchar : (2 : F) = 0) (hG : GoodCubicE d c0 c1) : Whiskers d (vS' d) (Wset d c0 c1) where
  not_inPi w hw hwPi := by
    obtain ⟨hne, z, hz0, hzPi, -⟩ := hw
    exact hne (no_second_line' hd hchar hz0 hzPi hwPi)
  opp w hw := by
    obtain ⟨hne, z, hz0, hzPi, -⟩ := hw
    exact slineZE_opp' hd hchar hz0 hzPi hne
  free p hp hfree w hw w' hw' hpw hpw' := by
    obtain ⟨m, -, huniq⟩ := exists_unique_wline_even hd hchar hG hp hfree
    exact (huniq w ⟨hw, hpw⟩).trans (huniq w' ⟨hw', hpw'⟩).symm

/-- **`|Wset| = q⁴ - q²`**, i.e. `|Wset| + q² = q⁴`. -/
theorem ncard_wsetE [Fintype F] {d c0 c1 : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (hchar : (2 : F) = 0)
    (hG : GoodCubicE d c0 c1) :
    (Wset d c0 c1).ncard + Fintype.card F ^ 2 = Fintype.card F ^ 4 := by
  have hq : 0 < Fintype.card F := Fintype.card_pos
  let g : SPt F → HLine F := fun p =>
    if h : p ∈ FreePtsE d then (exists_unique_wline_even hd hchar hG h.1 h.2).exists.choose else vStd'
  have hg : ∀ p ∈ FreePtsE d, g p ∈ Wset d c0 c1 ∧ hexInc p (g p) := by
    intro p hp
    simp only [g, dif_pos hp]
    exact (exists_unique_wline_even hd hchar hG hp.1 hp.2).exists.choose_spec
  have hfree_of_mem : ∀ w ∈ Wset d c0 c1, ∀ p : SPt F, hexInc p w → ¬ OnPiE d p → p ∈ FreePtsE d := by
    intro w hw p hpw hp
    refine ⟨hp, ?_⟩
    rintro ⟨M, hpM, r, hrv, hrM⟩
    exact (wset_whiskers_even hd hchar hG).opp w hw ⟨r, M, p, hrv, hrM, hpM, hpw⟩ |>.elim
  have := BipartiteDD.HexagonD.ncard_fiberwise (FreePtsE d) (Wset d c0 c1) g
    (fun p hp => (hg p hp).1) (Fintype.card F) (by
    intro w hw
    have : {a | a ∈ FreePtsE d ∧ g a = w} = {p : SPt F | hexInc p w ∧ ¬ OnPiE d p} := by
      ext p
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨hp, rfl⟩
        exact ⟨(hg p hp).2, hp.1⟩
      · rintro ⟨hpw, hpPi⟩
        have hp := hfree_of_mem w hw p hpw hpPi
        refine ⟨hp, ?_⟩
        obtain ⟨m, -, huniq⟩ := exists_unique_wline_even hd hchar hG hp.1 hp.2
        exact (huniq _ (hg p hp)).trans (huniq _ ⟨hw, hpw⟩).symm
    rw [this]
    exact ncard_offPiE hd hchar (fun hi => (wset_whiskers_even hd hchar hG).not_inPi w hw hi))
  have h2 := ncard_freeE hd hchar (d := d)
  rw [this] at h2
  have e : Fintype.card F * (Wset d c0 c1).ncard + Fintype.card F ^ 2 * (Fintype.card F + 1) +
      (Fintype.card F ^ 3 + 1) * (Fintype.card F + 1) =
      (Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4) := h2
  have : Fintype.card F * ((Wset d c0 c1).ncard + Fintype.card F ^ 2) =
      Fintype.card F * Fintype.card F ^ 4 := by
    nlinarith [e]
  exact Nat.eq_of_mul_eq_mul_left hq this

/-- **Theorem D (even `q ≥ 4`)**: a bipartite graph of maximum degree `≤ q + m`, diameter `≤ 6` on
`2(q+1)(q⁴+q²+1) + (m-1)(q⁴+2q³+q²+2q+2 + m(q³+q+2) + m²) + (m-1)(q⁴ - q²)` vertices. -/
theorem theoremD_even [Fintype F] (hchar : (2 : F) = 0) (hq : 4 ≤ Fintype.card F) {m : ℕ} (hm : 0 < m) :
    ∃ H : SimpleGraph (Fin (2 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) +
        (m - 1) * ((Fintype.card F ^ 4 + 2 * Fintype.card F ^ 3 + Fintype.card F ^ 2 +
          2 * Fintype.card F + 2) + m * (Fintype.card F ^ 3 + Fintype.card F + 2) + m ^ 2) +
        (m - 1) * (Fintype.card F ^ 4 - Fintype.card F ^ 2))),
      IsBipartiteDegDiam H (Fintype.card F + m) 6 := by
  obtain ⟨d, hd⟩ := exists_aniso_even hchar
  obtain ⟨c0, c1, hG⟩ := exists_goodCubicE hd hq hchar
  have hW := wset_whiskers_even hd hchar hG
  have hb := whiskers_bound_hexagon hd hchar hm (vS' d) hW
  have e : (Wset d c0 c1).ncard = Fintype.card F ^ 4 - Fintype.card F ^ 2 := by
    have := ncard_wsetE hd hchar hG
    omega
  rw [e] at hb
  exact hb

end BipartiteDD.HexagonEven
