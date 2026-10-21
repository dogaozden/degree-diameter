import BipartiteDD.HexagonD.Regular.Classes

/-! Theorem R instance, part 3a: the degrees of the versions.

`Dele x` says that the line version `x` has height at least `2` (so its line is an `S`-line or `v`) and a non-zero
last letter. The choice of `S` deletes only such versions (`Choice`). For a point version `⟨p, s⟩` and a line `l`
through `p`, the version `⟨l, extStr s 0 l⟩` is adjacent to it and is never deleted (`not_dele_kept`). So after the
deletion every point version still has at least `q + 1` neighbours, and every version has at least `q + 1`
neighbours before it (both from the `q + 1` lines or points through the underlying point or line).

Facts about heights used here: a point has height at most `2` (`ht_pt_le`), a line has height at most `3`, the
line `v` has height `3`, and a point of height `2` lies on `v` only, so it cannot lie on a line of height `2`
(`ht_pt_lt_of_inc`). -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon BipartiteDD.Doubling BipartiteDD.Regular
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)] {c : F}

local notation "GH" => Hexagon.incGraph (hexInc (F := F))

/-- The line versions that the choice of `S` may delete: height at least `2`, and last letter not `0`. -/
def Dele (c : F) (v : HLine F) (W : Set (HLine F)) (m : ℕ) (x : LnVer c v W m) : Prop :=
  2 ≤ ht c v W (Sum.inr x.1) ∧ ∃ a : Fin m, letter x.2 (ht c v W (Sum.inr x.1) - 1) = some a ∧ a.1 ≠ 0

theorem ht_line_le (v : SLine c) (W : Set (HLine F)) (l : HLine F) : ht c v.1 W (Sum.inr l) ≤ 3 :=
  height_le (A := lev c v.1 W) (by rw [lev_three]; exact Set.notMem_empty _)

/-- The line `v` has height `3`. -/
theorem ht_line_v (v : SLine c) (W : Set (HLine F)) : ht c v.1 W (Sum.inr v.1) = 3 := by
  apply le_antisymm (ht_line_le v W v.1)
  have h2 : 2 < ht c v.1 W (Sum.inr v.1) := (lt_ht_iff v W (Sum.inr v.1) 2).2 (by simp [lev, A2])
  omega

/-- A line other than `v` of height at least `2` has height exactly `2`. -/
theorem ht_line_ne (v : SLine c) (W : Set (HLine F)) (l : HLine F) (hl : l ≠ v.1)
    (h2 : 2 ≤ ht c v.1 W (Sum.inr l)) : ht c v.1 W (Sum.inr l) = 2 := by
  apply le_antisymm _ h2
  apply height_le (A := lev c v.1 W)
  simp [lev, A2, hl]

/-- A point lying on a line `l ≠ v` of height `2` has height at most `1`: it is not on `v`. -/
theorem ht_pt_lt_of_inc (hc : ¬ IsSquare (-c)) (v : SLine c) (W : Set (HLine F)) (p : SPt F) (l : HLine F)
    (hpl : hexInc p l) (hl2 : 2 ≤ ht c v.1 W (Sum.inr l)) :
    ht c v.1 W (Sum.inl p) < ht c v.1 W (Sum.inr l) := by
  by_cases hlv : l = v.1
  · rw [hlv, ht_line_v v W]
    have := ht_pt_le v W p
    omega
  · rw [ht_line_ne v W l hlv hl2]
    by_contra hp
    have hp2 : 1 < ht c v.1 W (Sum.inl p) := by
      have := ht_pt_le v W p
      omega
    have hp1 : Sum.inl p ∈ lev c v.1 W 1 := (lt_ht_iff v W (Sum.inl p) 1).1 hp2
    have hl1 : Sum.inr l ∈ lev c v.1 W 1 := (lt_ht_iff v W (Sum.inr l) 1).1 (by omega)
    simp only [lev, A1, inl_mem_sumSet, inr_mem_sumSet, Set.mem_ofPred_eq] at hp1 hl1
    have hOn : OnPi c p := onPi_of_mem (s := v) hp1
    have hp2' : hexInc p (⟨l, hl1⟩ : SLine c).1 := hpl
    have hu : v = (⟨l, hl1⟩ : SLine c) := (existsUnique_sline hc p hOn).unique hp1 hp2'
    exact hlv (congrArg Subtype.val hu).symm

/-- The string `extStr u s z w` agrees with `s` on the length of `s`. -/
theorem agree_extStr {V' : Type*} {h : V' → ℕ} {m : ℕ} (u : V') (s : Fin (h u) → Fin m) (z : Fin m) (w : V') :
    Agree s (extStr u s z w) := by
  intro i ha hb
  simp [extStr, ha]

section Kept

variable (v : SLine c) (W : Set (HLine F)) {m : ℕ}

/-- A point version is adjacent to the version `⟨l, extStr s 0 l⟩` of each line `l` through the point. -/
theorem levRel_pt_kept (hm : 0 < m) (p : SPt F) (s : Fin (ht c v.1 W (Sum.inl p)) → Fin m) (l : HLine F)
    (hpl : hexInc p l) :
    levRel c v.1 W m ⟨p, s⟩ ⟨l, extStr (Sum.inl p) s ⟨0, hm⟩ (Sum.inr l)⟩ :=
  ⟨(Hexagon.incGraph_adj_inl_inr).2 hpl, agree_extStr _ _ _ _⟩

/-- A line version is adjacent to the version `⟨p, extStr t 0 p⟩` of each point on the line. -/
theorem levRel_ln_kept (hm : 0 < m) (l : HLine F) (t : Fin (ht c v.1 W (Sum.inr l)) → Fin m) (p : SPt F)
    (hpl : hexInc p l) :
    levRel c v.1 W m ⟨p, extStr (Sum.inr l) t ⟨0, hm⟩ (Sum.inl p)⟩ ⟨l, t⟩ :=
  ⟨(Hexagon.incGraph_adj_inl_inr).2 hpl, (agree_extStr _ _ _ _).symm⟩

/-- The kept version of a line through a point version is not deleted, provided the line's last position lies
at or after the height of the point. -/
theorem not_dele_kept (hc : ¬ IsSquare (-c)) (hm : 0 < m) (p : SPt F) (s : Fin (ht c v.1 W (Sum.inl p)) → Fin m)
    (l : HLine F) (hpl : hexInc p l) :
    ¬ Dele c v.1 W m ⟨l, extStr (Sum.inl p) s ⟨0, hm⟩ (Sum.inr l)⟩ := by
  rintro ⟨hl2, a, ha, hne⟩
  have hkp := ht_pt_lt_of_inc hc v W p l hpl hl2
  have hlt : ht c v.1 W (Sum.inr l) - 1 < ht c v.1 W (Sum.inr l) := by omega
  rw [letter_of_lt _ hlt] at ha
  have ha2 : extStr (Sum.inl p) s ⟨0, hm⟩ (Sum.inr l) ⟨_, hlt⟩ = a := Option.some.inj ha
  by_cases hi : ht c v.1 W (Sum.inr l) - 1 < ht c v.1 W (Sum.inl p)
  · omega
  · have h0 : extStr (Sum.inl p) s ⟨0, hm⟩ (Sum.inr l) ⟨_, hlt⟩ = ⟨0, hm⟩ := by
      simp [extStr, hi]
    rw [h0] at ha2
    exact hne (by rw [← ha2])

/-- Every line version has at least `q + 1` neighbours among the point versions. -/
theorem ncard_degR_ge (hm : 0 < m) (l : HLine F) (t : Fin (ht c v.1 W (Sum.inr l)) → Fin m) :
    Fintype.card F + 1 ≤ {a : PtVer c v.1 W m | levRel c v.1 W m a ⟨l, t⟩}.ncard := by
  have hinj : Function.Injective
      (fun p : SPt F => (⟨p, extStr (Sum.inr l) t ⟨0, hm⟩ (Sum.inl p)⟩ : PtVer c v.1 W m)) :=
    fun p p' h => congrArg Sigma.fst h
  have hsub : (fun p : SPt F => (⟨p, extStr (Sum.inr l) t ⟨0, hm⟩ (Sum.inl p)⟩ : PtVer c v.1 W m)) ''
      {p : SPt F | hexInc p l} ⊆ {a : PtVer c v.1 W m | levRel c v.1 W m a ⟨l, t⟩} := by
    rintro _ ⟨p, hp, rfl⟩
    exact levRel_ln_kept v W hm l t p hp
  calc Fintype.card F + 1 = {p : SPt F | hexInc p l}.ncard := (ncard_hexInc_points l).symm
    _ = _ := (Set.ncard_image_of_injective _ hinj).symm
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

/-- Every point version has at least `q + 1` neighbours among the line versions that are not deleted. -/
theorem ncard_degL_restrict_ge (hc : ¬ IsSquare (-c)) (hm : 0 < m) (S : Set (LnVer c v.1 W m))
    (hS : ∀ x ∈ S, Dele c v.1 W m x) (p : SPt F) (s : Fin (ht c v.1 W (Sum.inl p)) → Fin m) :
    Fintype.card F + 1 ≤
      {b : {b : LnVer c v.1 W m // b ∉ S} | levRel c v.1 W m ⟨p, s⟩ b.1}.ncard := by
  set M := {b : {b : LnVer c v.1 W m // b ∉ S} | levRel c v.1 W m ⟨p, s⟩ b.1} with hM
  have hinj : Function.Injective
      (fun l : HLine F => (⟨l, extStr (Sum.inl p) s ⟨0, hm⟩ (Sum.inr l)⟩ : LnVer c v.1 W m)) :=
    fun l l' h => congrArg Sigma.fst h
  have hsub : (fun l : HLine F => (⟨l, extStr (Sum.inl p) s ⟨0, hm⟩ (Sum.inr l)⟩ : LnVer c v.1 W m)) ''
      {l : HLine F | hexInc p l} ⊆ Subtype.val '' M := by
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨⟨⟨l, extStr (Sum.inl p) s ⟨0, hm⟩ (Sum.inr l)⟩,
      fun hmem => not_dele_kept v W hc hm p s l hl (hS _ hmem)⟩, levRel_pt_kept v W hm p s l hl, rfl⟩
  calc Fintype.card F + 1 = {l : HLine F | hexInc p l}.ncard := (ncard_hexInc_lines p).symm
    _ = _ := (Set.ncard_image_of_injective _ hinj).symm
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = M.ncard := Set.ncard_image_of_injective _ Subtype.val_injective

end Kept

end BipartiteDD.HexagonD
