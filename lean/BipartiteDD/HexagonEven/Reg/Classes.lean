import BipartiteDD.HexagonEven.Reg.Relation

/-! Theorem R instance, part 2: the twin classes of the line versions.

`twinKey d v W m x` is the class of a line version `x = ⟨l, t⟩`: the line `l`, its first letter, and, for the
line `v` alone (height `3`), its second letter. Two versions with the same key have the same neighbourhood
(`levRel_twin`): a point of height at most `2` only compares the first two letters, and a point on a line `l ≠ v`
of height `≥ 2` cannot have height `2`, so the second letter is never compared for such a line. -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonEven

open BipartiteDD.HexagonD

open BipartiteDD.Hexagon BipartiteDD.Doubling BipartiteDD.Regular
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] {d : F}

local notation "GH" => Hexagon.incGraph (hexInc (F := F))

/-- The letter of a string at position `i`, or `none` past its end. -/
def letter {k m : ℕ} (t : Fin k → Fin m) (i : ℕ) : Option (Fin m) :=
  if h : i < k then some (t ⟨i, h⟩) else none

theorem letter_of_lt {k m : ℕ} (t : Fin k → Fin m) {i : ℕ} (h : i < k) :
    letter t i = some (t ⟨i, h⟩) := by
  simp [letter, h]

/-- The class of a line version: the line, its first letter, and its second letter when the line is `v`. -/
noncomputable def twinKey (d : F) (v : HLine F) (W : Set (HLine F)) (m : ℕ) (x : LnVer d v W m) :
    HLine F × Option (Fin m) × Option (Fin m) :=
  (x.1, letter x.2 0, if x.1 = v then letter x.2 1 else none)

/-- Agreement of two strings only looks at the positions that both have, so it is unchanged when the second
string changes at positions it shares with the first. -/
theorem agree_congr {m a b : ℕ} (s : Fin a → Fin m) (t t' : Fin b → Fin m)
    (h : ∀ i (_ha : i < a) (hb : i < b), t ⟨i, hb⟩ = t' ⟨i, hb⟩) :
    Agree s t ↔ Agree s t' := by
  constructor
  · intro hs i ha hb
    rw [← h i ha hb]
    exact hs i ha hb
  · intro hs i ha hb
    rw [h i ha hb]
    exact hs i ha hb

/-- Two line versions with the same key have the same neighbours among the point versions. -/
theorem ht_pt_le (v : SLineE d) (W : Set (HLine F)) (p : SPt F) : ht d v.1 W (Sum.inl p) ≤ 2 :=
  height_le (A := lev d v.1 W) (by simp [lev, A2])

/-- Two line versions with the same key have the same neighbours among the point versions. -/
theorem levRel_twin (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (hchar : (2 : F) = 0) (v : SLineE d) {W : Set (HLine F)} {m : ℕ}
    (b b' : LnVer d v.1 W m) (hb : twinKey d v.1 W m b = twinKey d v.1 W m b') (a : PtVer d v.1 W m) :
    levRel d v.1 W m a b ↔ levRel d v.1 W m a b' := by
  obtain ⟨l, t⟩ := b
  obtain ⟨l', t'⟩ := b'
  simp only [twinKey, Prod.mk.injEq] at hb
  obtain ⟨rfl, h0, h1⟩ := hb
  obtain ⟨p, s⟩ := a
  unfold levRel
  rw [levelled_adj, levelled_adj]
  refine and_congr_right fun hadj => agree_congr s t t' fun i ha hb => ?_
  have hi : i < 2 := lt_of_lt_of_le ha (ht_pt_le v W p)
  interval_cases i
  · have h := h0
    rw [letter_of_lt t hb, letter_of_lt t' hb] at h
    exact Option.some.inj h
  · by_cases hl : l = v.1
    · rw [if_pos hl, if_pos hl] at h1
      have h := h1
      rw [letter_of_lt t hb, letter_of_lt t' hb] at h
      exact Option.some.inj h
    · exfalso
      have hp1 : Sum.inl p ∈ lev d v.1 W 1 := (lt_ht_iff v W (Sum.inl p) 1).1 ha
      have hl1 : Sum.inr l ∈ lev d v.1 W 1 := (lt_ht_iff v W (Sum.inr l) 1).1 hb
      simp only [lev, A1, inl_mem_sumSet, inr_mem_sumSet, Set.mem_ofPred_eq] at hp1 hl1
      have hp2 : hexInc p (⟨l, hl1⟩ : SLineE d).1 := (Hexagon.incGraph_adj_inl_inr).1 hadj
      have hOn : OnPiE d p := onPi_of_mem (s := v) hp1
      have hu : v = (⟨l, hl1⟩ : SLineE d) := (existsUnique_slineE hd hchar p hOn).unique hp1 hp2
      exact hl (congrArg Subtype.val hu).symm

end BipartiteDD.HexagonEven
