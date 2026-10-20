import BipartiteDD.HexagonD.Levels

/-! Theorem D, slice 2, part 7: hypotheses (a), (b) of `delorme_levelled_polygon` for the levels `lev`. -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon BipartiteDD.Doubling Module Submodule

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)] {c : F}

local notation "GH" => Hexagon.incGraph (hexInc (F := F))

theorem lev_antitone (v : HLine F) (hv : InPi c v) (W : Set (HLine F)) : Antitone (lev c v W) := by
  refine antitone_nat_of_succ_le fun n => ?_
  rcases n with _ | _ | n
  · rintro (x | l) hx
    · simp only [lev, A1, inl_mem_sumSet, Set.mem_ofPred_eq] at hx
      simp only [lev, A0, inl_mem_sumSet, Set.mem_ofPred_eq]
      exact hv _ hx
    · simp only [lev, A1, inr_mem_sumSet, Set.mem_ofPred_eq] at hx
      simp only [lev, A0, inr_mem_sumSet, Set.mem_ofPred_eq]
      exact Or.inl hx
  · rintro x hx
    simp only [lev, A2, Set.mem_singleton_iff] at hx
    subst hx
    simp [lev, A1, hv]
  · intro x hx
    simp [lev] at hx ⊢

theorem lev_three (v : HLine F) (W : Set (HLine F)) : lev c v W 3 = ∅ := rfl

theorem Whiskers.not_meets {v : SLine c} {W : Set (HLine F)} (hW : Whiskers c v W) {w : HLine F}
    (hw : w ∈ W) : ¬ Meets v.1 w := fun ⟨r, h1, h2⟩ => hW.opp w hw ⟨r, w, r, h1, h2, h2, h2⟩

theorem ncard_le_one_of {α : Type*} [Finite α] {s : Set α} (h : ∀ a ∈ s, ∀ b ∈ s, a = b) :
    s.ncard ≤ 1 :=
  (Set.ncard_le_one_iff_subsingleton).2 h

section

variable (hc : ¬ IsSquare (-c)) {v : SLine c} {W : Set (HLine F)}

include hc

theorem lev_ha1 (i : ℕ) : ∀ x ∈ lev c v.1 W (i + 1), ∀ u, (GH).Adj u x → u ∈ lev c v.1 W i := by
  rcases i with _ | _ | i
  · rintro (p | l) hx (p' | l') hu
    · exact absurd hu Hexagon.incGraph_not_adj_inl_inl
    · simp only [lev, A1, inl_mem_sumSet, Set.mem_ofPred_eq] at hx
      have hu' : hexInc p l' := Hexagon.incGraph_adj_inr_inl.1 hu.symm
      simp only [lev, A0, inr_mem_sumSet, Set.mem_ofPred_eq]
      exact Or.inr (Or.inl ⟨p, hx, hu'⟩)
    · simp only [lev, A1, inr_mem_sumSet, Set.mem_ofPred_eq] at hx
      have hu' : hexInc p' l := Hexagon.incGraph_adj_inl_inr.1 hu
      simp only [lev, A0, inl_mem_sumSet, Set.mem_ofPred_eq]
      exact hx _ hu'
    · exact absurd hu Hexagon.incGraph_not_adj_inr_inr
  · rintro x hx (p' | l') hu
    · simp only [lev, A2, Set.mem_singleton_iff] at hx
      subst hx
      have hu' : hexInc p' v.1 := Hexagon.incGraph_adj_inl_inr.1 hu.symm
      simp only [lev, A1, inl_mem_sumSet, Set.mem_ofPred_eq]
      exact hu'
    · simp only [lev, A2, Set.mem_singleton_iff] at hx
      subst hx
      exact absurd hu Hexagon.incGraph_not_adj_inr_inr
  · intro x hx
    simp [lev] at hx

theorem lev_ha2 (i : ℕ) : ∀ u ∈ lev c v.1 W i, u ∉ lev c v.1 W (i + 1) →
    ((GH).neighborSet u ∩ lev c v.1 W (i + 1)).ncard ≤ 1 := by
  rcases i with _ | _ | _ | i
  · rintro (p | l) hu hnu
    · simp only [lev, A0, A1, inl_mem_sumSet, Set.mem_ofPred_eq] at hu hnu
      refine ncard_le_one_of ?_
      rintro (p₁ | l₁) ⟨h1, h1'⟩ (p₂ | l₂) ⟨h2, h2'⟩
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h2 (by simp)
      · simp only [SimpleGraph.mem_neighborSet, Hexagon.incGraph_adj_inl_inr] at h1 h2
        simp only [lev, A1, inr_mem_sumSet, Set.mem_ofPred_eq] at h1' h2'
        rw [eq_of_inPi_of_mem hc h1' h2' h1 h2]
    · simp only [lev, A0, A1, inr_mem_sumSet, Set.mem_ofPred_eq] at hu hnu
      refine ncard_le_one_of ?_
      rintro (p₁ | l₁) ⟨h1, h1'⟩ (p₂ | l₂) ⟨h2, h2'⟩
      · simp only [SimpleGraph.mem_neighborSet, Hexagon.incGraph_adj_inr_inl] at h1 h2
        simp only [lev, A1, inl_mem_sumSet, Set.mem_ofPred_eq] at h1' h2'
        by_contra hne
        have hne' : p₁ ≠ p₂ := fun h => hne (by rw [h])
        have := eq_of_digon genPolygonGraph_hexagon hne' h1' h2' h1 h2
        exact hnu (this ▸ v.2)
      · exact absurd h2 (by simp)
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
  · rintro u hu hnu
    refine ncard_le_one_of ?_
    rintro a ⟨-, ha⟩ b ⟨-, hb⟩
    simp only [lev, A2, Set.mem_singleton_iff] at ha hb
    rw [ha, hb]
  · rintro u hu _
    refine ncard_le_one_of ?_
    rintro a ⟨-, ha⟩
    simp [lev] at ha
  · rintro u hu _
    simp [lev] at hu

theorem lev_hb (hW : Whiskers c v W) : ∀ u, u ∉ lev c v.1 W 0 →
    ((GH).neighborSet u ∩ lev c v.1 W 0).ncard ≤ 1 := by
  rintro (p | l) hu
  · simp only [lev, A0, inl_mem_sumSet, Set.mem_ofPred_eq] at hu
    refine ncard_le_one_of ?_
    rintro (p₁ | l₁) ⟨h1, h1'⟩ (p₂ | l₂) ⟨h2, h2'⟩
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)
    · exact absurd h2 (by simp)
    · simp only [SimpleGraph.mem_neighborSet, Hexagon.incGraph_adj_inl_inr] at h1 h2
      simp only [lev, A0, inr_mem_sumSet, Set.mem_ofPred_eq] at h1' h2'
      have hpv : ¬ hexInc p v.1 := fun h => hu (onPi_of_mem h)
      have hnotPi : ∀ l, hexInc p l → ¬ InPi c l := fun l hl hi => hu (hi _ hl)
      have key : ∀ l, hexInc p l → (Meets v.1 l ∨ l ∈ W) → ∀ l', hexInc p l' →
          (Meets v.1 l' ∨ l' ∈ W) → l = l' := by
        rintro l hl (⟨r, hr, hrl⟩ | hlW) l' hl' (⟨r', hr', hrl'⟩ | hlW')
        · exact eq_of_triangle genPolygonGraph_hexagon hpv hl hrl hr hl' hrl' hr'
        · exact absurd ⟨r, l, p, hr, hrl, hl, hl'⟩ (hW.opp l' hlW')
        · exact absurd ⟨r', l', p, hr', hrl', hl', hl⟩ (hW.opp l hlW)
        · refine hW.free p hu ?_ l hlW l' hlW' hl hl'
          rintro ⟨M, hM, r, hrv, hrM⟩
          exact hW.opp l hlW ⟨r, M, p, hrv, hrM, hM, hl⟩
      have e1 : Meets v.1 l₁ ∨ l₁ ∈ W := h1'.resolve_left (hnotPi _ h1)
      have e2 : Meets v.1 l₂ ∨ l₂ ∈ W := h2'.resolve_left (hnotPi _ h2)
      rw [key l₁ h1 e1 l₂ h2 e2]
  · simp only [lev, A0, inr_mem_sumSet, Set.mem_ofPred_eq, not_or] at hu
    refine ncard_le_one_of ?_
    rintro (p₁ | l₁) ⟨h1, h1'⟩ (p₂ | l₂) ⟨h2, h2'⟩
    · simp only [SimpleGraph.mem_neighborSet, Hexagon.incGraph_adj_inr_inl] at h1 h2
      simp only [lev, A0, inl_mem_sumSet, Set.mem_ofPred_eq] at h1' h2'
      rw [eq_of_onPi_of_not_inPi h1' h2' h1 h2 hu.1]
    · exact absurd h2 (by simp)
    · exact absurd h1 (by simp)
    · exact absurd h1 (by simp)

end

end BipartiteDD.HexagonD
