import BipartiteDD.HexagonD.Regular.Kept
import BipartiteDD.Regular.Completion

/-! Theorem R instance, part 3b: the choice of the deleted line versions.

`Ldel Q` is the set of `InPi` lines outside `Q`, where `Q` is a set of `q` lines of `InPi ∖ {v}`. `delSet L` is
the set of `Dele` versions of the lines in `L`. Its size is `(m - 1) m (q³ - q + m)`, the excess of the line side
over the point side (`card_delSet_eq`). Each twin class of line versions that contains a deleted version keeps a
version with last letter `0`, which is not deleted (`hclass`), so the class condition of `regular_of_twin_classes`
holds. -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon BipartiteDD.Doubling BipartiteDD.Regular Finset
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)] {c : F}

section Strings

variable {m : ℕ}

/-- Strings of length `n + 1` whose last letter satisfies `P`: `m ^ n` for each letter. -/
theorem card_filter_last (n : ℕ) (P : Fin m → Prop) [DecidablePred P] :
    (univ.filter (fun t : Fin (n + 1) → Fin m => P (t (Fin.last n)))).card =
      (univ.filter P).card * m ^ n := by
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_mul]
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n + 1) => Fin m))]
  rw [Fintype.sum_prod_type]
  simp only [Fin.snocEquiv_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : P a <;> simp [h, Fin.snoc_last, Finset.sum_const, Finset.card_univ, Fintype.card_fin]

theorem card_ne_zero_fin (hm : 0 < m) : (univ.filter (fun a : Fin m => a.1 ≠ 0)).card = m - 1 := by
  have : univ.filter (fun a : Fin m => a.1 ≠ 0) = univ.erase ⟨0, hm⟩ := by
    ext a
    simp [Fin.ext_iff]
  rw [this, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]

/-- Strings of length `k ≥ 1` whose last letter is not `0`: `m ^ (k - 1) (m - 1)` of them. -/
theorem card_last_ne (hm : 0 < m) (k : ℕ) (hk : 1 ≤ k) :
    (univ.filter (fun t : Fin k → Fin m => ∃ a : Fin m, letter t (k - 1) = some a ∧ a.1 ≠ 0)).card =
      m ^ (k - 1) * (m - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have key : ∀ t : Fin (n + 1) → Fin m,
      (∃ a : Fin m, letter t n = some a ∧ a.1 ≠ 0) ↔ (t (Fin.last n)).1 ≠ 0 := by
    intro t
    rw [letter_of_lt t (Nat.lt_succ_self n)]
    exact ⟨fun ⟨a, ha, h⟩ => by cases ha; exact h, fun h => ⟨_, rfl, h⟩⟩
  simp only [Nat.add_sub_cancel]
  rw [Finset.filter_congr (fun t _ => key t), card_filter_last n (fun a : Fin m => a.1 ≠ 0),
    card_ne_zero_fin hm, mul_comm]

end Strings

section Choice

variable {m : ℕ} [Fintype (HLine F)] (v : SLine c) (W : Set (HLine F))

/-- The `InPi` lines outside `Q`. -/
noncomputable def Ldel (c : F) (Q : Finset (HLine F)) : Finset (HLine F) :=
  univ.filter (fun l => InPi c l ∧ l ∉ Q)

/-- The line versions that the choice deletes: the `Dele` versions of the lines in `L`. -/
noncomputable def delSet (m : ℕ) (L : Finset (HLine F)) : Finset (LnVer c v.1 W m) :=
  univ.filter (fun x => Dele c v.1 W m x ∧ x.1 ∈ L)

theorem ldel_eq (Q : Finset (HLine F)) : Ldel c Q = univ.filter (InPi c) \ Q := by
  ext l
  simp [Ldel]

/-- A line of `InPi` has height at least `2`. -/
theorem two_le_ht_of_inPi (l : HLine F) (hl : InPi c l) : 2 ≤ ht c v.1 W (Sum.inr l) := by
  have h1 : 1 < ht c v.1 W (Sum.inr l) :=
    (lt_ht_iff v W (Sum.inr l) 1).2 (by simp [lev, A1, hl])
  omega

theorem card_delSet (hm : 0 < m) (L : Finset (HLine F)) (hL : ∀ l ∈ L, 2 ≤ ht c v.1 W (Sum.inr l)) :
    (delSet v W m L).card = ∑ l ∈ L, m ^ (ht c v.1 W (Sum.inr l) - 1) * (m - 1) := by
  have inner : ∀ l : HLine F,
      (∑ t : Fin (ht c v.1 W (Sum.inr l)) → Fin m,
        if Dele c v.1 W m ⟨l, t⟩ ∧ l ∈ L then 1 else 0) =
        if l ∈ L then m ^ (ht c v.1 W (Sum.inr l) - 1) * (m - 1) else 0 := by
    intro l
    by_cases hl : l ∈ L
    · have h2 := hL l hl
      rw [if_pos hl]
      simp only [hl, and_true]
      rw [Finset.sum_boole, ← card_last_ne hm _ (by omega)]
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro t _
      simp only [Dele, h2, true_and]
    · rw [if_neg hl]
      simp [hl]
  unfold delSet
  rw [Finset.card_filter, Fintype.sum_sigma]
  refine (Finset.sum_congr rfl fun l _ => inner l).trans ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- The size of `Ldel Q` when `Q` lies in `InPi`. -/
theorem card_ldel (hc : ¬ IsSquare (-c)) (Q : Finset (HLine F)) (hQ : ∀ l ∈ Q, InPi c l) :
    (Ldel c Q).card + Q.card = Fintype.card F ^ 3 + 1 := by
  have hsub : Q ⊆ univ.filter (InPi c) := fun l hl => by simp [hQ l hl]
  rw [ldel_eq, Finset.card_sdiff_add_card_eq_card hsub, ← ncard_setOf_eq_card_filter, ncard_sline hc]

/-- `Q`: a set of `q` lines of `InPi` other than `v`. -/
theorem exists_Q (hc : ¬ IsSquare (-c)) : ∃ Q : Finset (HLine F),
    Q ⊆ (univ.filter (InPi c)).erase v.1 ∧ Q.card = Fintype.card F := by
  have hX : ((univ.filter (InPi c)).erase v.1).card = Fintype.card F ^ 3 := by
    have hv : v.1 ∈ univ.filter (InPi c) := by simp [v.2]
    rw [card_erase_of_mem hv, ← ncard_setOf_eq_card_filter, ncard_sline hc]
    simp
  have hq : Fintype.card F ≤ Fintype.card F ^ 3 := Nat.le_self_pow (by norm_num) _
  obtain ⟨Q, hQ, hcard⟩ := Finset.exists_subset_card_eq (s := (univ.filter (InPi c)).erase v.1)
    (n := Fintype.card F) (by omega)
  exact ⟨Q, hQ, hcard⟩

/-- The size of the deleted set: `(m - 1) m (q³ - q + m)`. -/
theorem card_delSet_eq (hc : ¬ IsSquare (-c)) (hm : 0 < m) (Q : Finset (HLine F))
    (hQ : Q ⊆ (univ.filter (InPi c)).erase v.1) (hcard : Q.card = Fintype.card F) :
    (delSet v W m (Ldel c Q)).card = (m - 1) * m * (Fintype.card F ^ 3 - Fintype.card F + m) := by
  have hQI : ∀ l ∈ Q, InPi c l := fun l hl => (mem_filter.1 (mem_of_mem_erase (hQ hl))).2
  have hv : v.1 ∈ Ldel c Q := by
    refine mem_filter.2 ⟨mem_univ _, v.2, fun h => ?_⟩
    exact (mem_erase.1 (hQ h)).1 rfl
  have hLht : ∀ l ∈ Ldel c Q, 2 ≤ ht c v.1 W (Sum.inr l) := fun l hl =>
    two_le_ht_of_inPi v W l (mem_filter.1 hl).2.1
  have hL := card_ldel hc Q hQI
  have hq : Fintype.card F ≤ Fintype.card F ^ 3 := Nat.le_self_pow (by norm_num) _
  have hB : (Ldel c Q).card - 1 = Fintype.card F ^ 3 - Fintype.card F := by omega
  have hrest : ∀ l ∈ (Ldel c Q).erase v.1, m ^ (ht c v.1 W (Sum.inr l) - 1) * (m - 1) = m * (m - 1) := by
    intro l hl
    rw [ht_line_ne v W l (ne_of_mem_erase hl) (hLht l (mem_of_mem_erase hl))]
    simp
  rw [card_delSet v W hm _ hLht, ← Finset.add_sum_erase _ _ hv, ht_line_v v W,
    Finset.sum_congr rfl hrest, Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hv, hB]
  simp only [show (3 : ℕ) - 1 = 2 from rfl]
  ring

section Class

variable {m : ℕ} (v : SLine c) (W : Set (HLine F))

/-- The version with the same line and first letters, whose last letter is `0`. -/
noncomputable def repLast (hm : 0 < m) (x : LnVer c v.1 W m) : LnVer c v.1 W m :=
  ⟨x.1, fun i => if i.1 + 1 = ht c v.1 W (Sum.inr x.1) then ⟨0, hm⟩ else x.2 i⟩

theorem letter_repLast (hm : 0 < m) (x : LnVer c v.1 W m) (i : ℕ)
    (hi : i + 1 ≠ ht c v.1 W (Sum.inr x.1)) :
    letter (repLast v W hm x).2 i = letter x.2 i := by
  by_cases h : i < ht c v.1 W (Sum.inr x.1)
  · simp [letter, repLast, h, hi]
  · have h' : ¬ i < ht c v.1 W (Sum.inr (repLast v W hm x).1) := h
    simp [letter, h, h']

theorem not_dele_repLast (hm : 0 < m) (x : LnVer c v.1 W m) :
    ¬ Dele c v.1 W m (repLast v W hm x) := by
  rintro ⟨h2, a, ha, hne⟩
  have hlast : letter (repLast v W hm x).2 (ht c v.1 W (Sum.inr (repLast v W hm x).1) - 1) =
      some ⟨0, hm⟩ := by
    have h2' : 2 ≤ ht c v.1 W (Sum.inr x.1) := h2
    have hlt : ht c v.1 W (Sum.inr x.1) - 1 < ht c v.1 W (Sum.inr x.1) := by omega
    have hk : ht c v.1 W (Sum.inr x.1) - 1 + 1 = ht c v.1 W (Sum.inr x.1) := by omega
    simp [letter, repLast, hlt, hk]
  rw [hlast] at ha
  have : a = ⟨0, hm⟩ := (Option.some.inj ha).symm
  exact hne (by rw [this])

theorem twinKey_repLast (hm : 0 < m) (x : LnVer c v.1 W m) (hx : Dele c v.1 W m x) :
    twinKey c v.1 W m (repLast v W hm x) = twinKey c v.1 W m x := by
  have h2 : 2 ≤ ht c v.1 W (Sum.inr x.1) := hx.1
  have hA : letter (repLast v W hm x).2 0 = letter x.2 0 :=
    letter_repLast v W hm x 0 (by omega)
  have hB : x.1 = v.1 → letter (repLast v W hm x).2 1 = letter x.2 1 := fun hv =>
    letter_repLast v W hm x 1 (by
      have := ht_line_v v W
      rw [hv]
      omega)
  show (x.1, letter (repLast v W hm x).2 0, if x.1 = v.1 then letter (repLast v W hm x).2 1 else none) =
    (x.1, letter x.2 0, if x.1 = v.1 then letter x.2 1 else none)
  rw [hA]
  by_cases hv : x.1 = v.1
  · rw [if_pos hv, if_pos hv, hB hv]
  · rw [if_neg hv, if_neg hv]

/-- The class of a line version: its twin key. -/
noncomputable def cls (x : LnVer c v.1 W m) : {k // ∃ y : LnVer c v.1 W m, twinKey c v.1 W m y = k} :=
  ⟨twinKey c v.1 W m x, x, rfl⟩

/-- Every version has a version in its class that is not deleted. -/
theorem exists_not_dele (hm : 0 < m) (y : LnVer c v.1 W m) :
    ∃ z : LnVer c v.1 W m, twinKey c v.1 W m z = twinKey c v.1 W m y ∧ ¬ Dele c v.1 W m z := by
  by_cases hD : Dele c v.1 W m y
  · exact ⟨repLast v W hm y, twinKey_repLast v W hm y hD, not_dele_repLast v W hm y⟩
  · exact ⟨y, rfl, hD⟩

/-- The class condition of `regular_of_twin_classes` for the deleted set `delSet L`: every class keeps a version. -/
theorem hclass (hm : 0 < m) (L : Finset (HLine F)) (k : {k // ∃ y : LnVer c v.1 W m, twinKey c v.1 W m y = k}) :
    ((delSet v W m L).filter (fun b => cls v W b = k)).card <
      (univ.filter (fun b => cls v W b = k)).card := by
  obtain ⟨y, hy⟩ := k.2
  obtain ⟨z, hzk, hzD⟩ := exists_not_dele v W hm y
  have hzcls : cls v W z = k := Subtype.ext (hzk.trans hy)
  have hsub : (delSet v W m L).filter (fun b => cls v W b = k) ⊆ univ.filter (fun b => cls v W b = k) := by
    intro x hx
    simp only [mem_filter] at hx ⊢
    exact ⟨mem_univ _, hx.2⟩
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset hsub]
  refine ⟨z, ?_, ?_⟩
  · simp only [mem_filter, mem_univ, true_and]
    exact hzcls
  · intro hmem
    simp only [mem_filter, mem_univ, true_and, delSet] at hmem
    exact hzD hmem.1.1

end Class

end Choice

end BipartiteDD.HexagonD
