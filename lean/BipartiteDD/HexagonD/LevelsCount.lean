import BipartiteDD.HexagonD.LevelsHyp
import BipartiteDD.HexagonD.LevelsForest

/-! Theorem D, slice 2, part 9: the sizes of the levels.

With `q = |F|`: `|A₂| = 1`, `|A₁| = q³ + q + 2`, `|A₀| = q⁴ + 2q³ + q² + 2q + 2 + |W|`. -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon BipartiteDD.Doubling Module Submodule
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)] {c : F}

theorem ncard_hexInc_points (l : HLine F) : {p : SPt F | hexInc p l}.ncard = Fintype.card F + 1 := by
  rw [← Nat.card_coe_set_eq]
  exact card_points_hline l

theorem ncard_hexInc_lines (p : SPt F) : {l : HLine F | hexInc p l}.ncard = Fintype.card F + 1 := by
  rw [← Nat.card_coe_set_eq]
  exact card_lines_through p

theorem ncard_onPi (hc : ¬ IsSquare (-c)) :
    {p : SPt F | OnPi c p}.ncard = (Fintype.card F ^ 3 + 1) * (Fintype.card F + 1) := by
  rw [← Nat.card_coe_set_eq]
  show Nat.card (PtPi c) = _
  rw [Nat.card_eq_fintype_card]
  exact card_pointsPi hc

theorem ncard_sline (hc : ¬ IsSquare (-c)) : {l : HLine F | InPi c l}.ncard = Fintype.card F ^ 3 + 1 := by
  rw [← Nat.card_coe_set_eq]
  show Nat.card (SLine c) = _
  rw [Nat.card_eq_fintype_card]
  exact card_sline hc

theorem ncard_meets (hc : ¬ IsSquare (-c)) (v : SLine c) :
    {l : HLine F | Meets v.1 l ∧ ¬ InPi c l}.ncard = Fintype.card F * (Fintype.card F + 1) := by
  have hset : {l : HLine F | Meets v.1 l ∧ ¬ InPi c l} = {l | Meets v.1 l ∧ l ≠ v.1} := by
    ext l
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h2 (h ▸ v.2)⟩
    · rintro ⟨⟨r, hr, hrl⟩, h2⟩
      refine ⟨⟨r, hr, hrl⟩, fun hl => h2 ?_⟩
      exact (eq_of_inPi_of_mem hc v.2 hl hr hrl).symm
  rw [hset, ← Nat.card_coe_set_eq]
  let e : (Σ r : {r : SPt F // hexInc r v.1}, {l : HLine F // hexInc r.1 l ∧ l ≠ v.1}) ≃
      {l : HLine F | Meets v.1 l ∧ l ≠ v.1} :=
    Equiv.ofBijective (fun x => ⟨x.2.1, ⟨x.1.1, x.1.2, x.2.2.1⟩, x.2.2.2⟩) (by
      constructor
      · rintro ⟨⟨r, hr⟩, ⟨l, hl, hlv⟩⟩ ⟨⟨r', hr'⟩, ⟨l', hl', hlv'⟩⟩ h
        have hll : l = l' := congrArg Subtype.val h
        subst hll
        have hrr : r = r' := by
          by_contra hne
          exact hlv (eq_of_digon genPolygonGraph_hexagon hne hl hl' hr hr')
        subst hrr
        rfl
      · rintro ⟨l, ⟨r, hr, hrl⟩, hlv⟩
        exact ⟨⟨⟨r, hr⟩, ⟨l, hrl, hlv⟩⟩, rfl⟩)
  rw [← Nat.card_congr e, Nat.card_sigma]
  have hfib : ∀ r : {r : SPt F // hexInc r v.1}, Nat.card {l : HLine F // hexInc r.1 l ∧ l ≠ v.1} =
      Fintype.card F := by
    intro r
    have h1 : {l : HLine F | hexInc r.1 l ∧ l ≠ v.1} = {l | hexInc r.1 l} \ {v.1} := by
      ext l; simp
    show Nat.card ↑{l : HLine F | hexInc r.1 l ∧ l ≠ v.1} = _
    rw [Nat.card_coe_set_eq, h1, Set.ncard_sdiff_singleton_of_mem (show v.1 ∈ {l : HLine F | hexInc r.1 l} from r.2), ncard_hexInc_lines]
    rfl
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have : Fintype.card {r : SPt F // hexInc r v.1} = Fintype.card F + 1 := by
    rw [← Nat.card_eq_fintype_card]; exact card_points_hline v.1
  rw [this]; ring

end BipartiteDD.HexagonD
