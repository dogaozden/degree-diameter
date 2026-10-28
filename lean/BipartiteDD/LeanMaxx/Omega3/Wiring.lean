import Mathlib

/-!
# Gómez's wiring: blocks, hub classes, and the families of Theorem 3.3

There are `α` blocks of five copies; a copy is `(b, i)` with `b : Fin α` and `i : ZMod 5`. Block `b` has
type `typ b` (`false` = type a, `true` = type b of the note). A hub class is `(bar, k)`, `bar : Bool`
(`false` = unbarred, `true` = barred), `k : ZMod 5`; it meets in block `b` the two copies

* type a, unbarred: `k - 1, k + 1`;   type a, barred: `k + 2, k + 3`;
* type b, unbarred: `k + 3, k + 4`;   type b, barred: `k - 1, k + 1`.

For an unbarred class `k` and a copy `c'` it misses, `F0 … F3` are the families of copies that index the
radius-4 and radius-2 balls in Theorem 3.3 (`Route.lean` shows they cover). `m2` counts the radius-2 ones.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace BipartiteDD.LeanMaxx.Omega3

open Finset

/-- A copy: a block and a position in `ZMod 5`. -/
abbrev Copy (α : ℕ) := Fin α × ZMod 5

/-- Positions met by hub class `(bar, k)` in a block of type `ty`. -/
def metPos (ty bar : Bool) (k i : ZMod 5) : Bool :=
  match ty, bar with
  | false, false => decide (i = k - 1 ∨ i = k + 1)
  | false, true => decide (i = k + 2 ∨ i = k + 3)
  | true, false => decide (i = k + 3 ∨ i = k + 4)
  | true, true => decide (i = k - 1 ∨ i = k + 1)

variable {α : ℕ} (typ : Fin α → Bool)

/-- Hub class `(bar, k)` meets copy `c`. -/
def meets (bar : Bool) (k : ZMod 5) (c : Copy α) : Bool := metPos (typ c.1) bar k c.2

/-- Two distinct copies share a hub class of the given bar. -/
def share (bar : Bool) (c d : Copy α) : Bool :=
  decide (c ≠ d) && decide (∃ k : ZMod 5, meets typ bar k c = true ∧ meets typ bar k d = true)

/-- The copies met by the unbarred class `k`. -/
def CuK (k : ZMod 5) : Finset (Copy α) := univ.filter fun c => meets typ false k c

/-- `F0`: copies of `CuK k` sharing a barred class with `c'` (radius-4 centres). -/
def F0 (k : ZMod 5) (c' : Copy α) : Finset (Copy α) := (CuK typ k).filter fun c₁ => share typ true c₁ c'

/-- `F1`: copies `x` with `c₁ ~u x ~b c'` for some `c₁ ∈ CuK k`. -/
def F1 (k : ZMod 5) (c' : Copy α) : Finset (Copy α) :=
  univ.filter fun x => decide (∃ c₁ ∈ CuK typ k, share typ false c₁ x = true) && share typ true x c'

/-- `F2`: pairs `(c₁, x)` with `c₁ ∈ CuK k`, `c₁ ~b x ~u c'`. -/
def F2 (k : ZMod 5) (c' : Copy α) : Finset (Copy α × Copy α) :=
  (CuK typ k ×ˢ (univ : Finset (Copy α))).filter fun p => share typ true p.1 p.2 && share typ false p.2 c'

/-- `F3`: copies `c₁ ∈ CuK k` joined to `c'` by two barred passes. -/
def F3 (k : ZMod 5) (c' : Copy α) : Finset (Copy α) :=
  (CuK typ k).filter fun c₁ => decide (∃ x, share typ true c₁ x = true ∧ share typ true x c' = true)

/-- The number of radius-2 balls to be counted. -/
def m2 (k : ZMod 5) (c' : Copy α) : ℕ := (F1 typ k c').card + (F2 typ k c').card + (F3 typ k c' \ F0 typ k c').card

/-- First block of type a (`false`), if any. -/
def firstA (typ : Fin α → Bool) : Option (Fin α) := (List.finRange α).find? fun b => !typ b

/-- The missed copy of Lemma 3.2 for the unbarred class `0`. -/
def cstar (hα : 0 < α) : Copy α :=
  match firstA typ with
  | some b => (b, 3)
  | none => (⟨0, hα⟩, 0)


/-! ### Basic facts -/

theorem share_comm (bar : Bool) (c d : Copy α) : share typ bar c d = share typ bar d c := by
  simp only [share, ne_comm, and_comm]

theorem mem_CuK {k : ZMod 5} {c : Copy α} : c ∈ CuK typ k ↔ meets typ false k c = true := by
  simp [CuK]

theorem mem_F0 {k : ZMod 5} {c' c : Copy α} :
    c ∈ F0 typ k c' ↔ meets typ false k c = true ∧ share typ true c c' = true := by
  simp [F0, CuK]

theorem F0_subset (k : ZMod 5) (c' : Copy α) : F0 typ k c' ⊆ CuK typ k := fun _ h => (Finset.mem_filter.1 h).1

theorem F3_subset (k : ZMod 5) (c' : Copy α) : F3 typ k c' ⊆ CuK typ k := fun _ h => (Finset.mem_filter.1 h).1

/-- Each hub class meets exactly two positions in a block. -/
theorem card_pos (ty bar : Bool) (k : ZMod 5) : ((univ : Finset (ZMod 5)).filter fun i => metPos ty bar k i = true).card = 2 := by
  revert ty bar k; decide

/-- A copy is met by exactly two hub classes of each bar. -/
theorem card_cls (ty bar : Bool) (i : ZMod 5) : ((univ : Finset (ZMod 5)).filter fun k => metPos ty bar k i = true).card = 2 := by
  revert ty bar i; decide

/-- A hub class meets exactly `2 α` copies. -/
theorem card_meets (bar : Bool) (k : ZMod 5) : ((univ : Finset (Copy α)).filter fun c => meets typ bar k c = true).card = 2 * α := by
  have : (univ : Finset (Copy α)).filter (fun c => meets typ bar k c = true) =
      (univ : Finset (Fin α)).biUnion fun b =>
        ((univ : Finset (ZMod 5)).filter fun i => metPos (typ b) bar k i = true).image fun i => (b, i) := by
    ext ⟨b, i⟩
    rw [Finset.mem_filter]
    simp only [meets, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
      Prod.mk.injEq]
    constructor
    · intro h; exact ⟨b, i, h, rfl, rfl⟩
    · rintro ⟨b', i', h, rfl, rfl⟩; exact h
  rw [this, Finset.card_biUnion]
  · simp [card_pos, Finset.card_image_of_injective _ (Prod.mk_right_injective _)]
    ring
  · intro b _ b' _ hbb'
    rw [Function.onFun, Finset.disjoint_left]
    intro c hc hc'
    simp only [Finset.mem_image] at hc hc'
    obtain ⟨i, _, rfl⟩ := hc
    obtain ⟨i', _, h⟩ := hc'
    exact hbb' (Prod.mk.inj h).1.symm

theorem card_CuK (k : ZMod 5) : (CuK typ k).card = 2 * α := card_meets typ false k

/-- A copy shares a hub class (of one bar) with at most `4 α` copies. -/
theorem card_share_le (bar : Bool) (c : Copy α) :
    ((univ : Finset (Copy α)).filter fun d => share typ bar c d = true).card ≤ 4 * α := by
  have hsub : (univ : Finset (Copy α)).filter (fun d => share typ bar c d = true) ⊆
      ((univ : Finset (ZMod 5)).filter fun k => metPos (typ c.1) bar k c.2 = true).biUnion
        fun k => (univ : Finset (Copy α)).filter fun d => meets typ bar k d = true := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, share, Bool.and_eq_true, decide_eq_true_eq] at hd
    obtain ⟨_, k, hk1, hk2⟩ := hd
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨k, hk1, hk2⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  rw [Finset.sum_congr rfl (fun k _ => card_meets typ bar k)]
  rw [Finset.sum_const, card_cls]
  simp; omega

/-! ### Lemma 3.2: the missed copy -/

theorem firstA_some {b : Fin α} (h : firstA typ = some b) : typ b = false := by
  unfold firstA at h
  have := List.find?_some h
  simpa using this

theorem firstA_none (h : firstA typ = none) (b : Fin α) : typ b = true := by
  unfold firstA at h
  have := List.find?_eq_none.1 h b (List.mem_finRange b)
  simpa using this

theorem cstar_none (hα : 0 < α) (h : firstA typ = none) : cstar typ hα = (⟨0, hα⟩, 0) := by
  unfold cstar; rw [h]

theorem cstar_some (hα : 0 < α) {b : Fin α} (h : firstA typ = some b) : cstar typ hα = (b, 3) := by
  unfold cstar; rw [h]

theorem cstar_not_mem (hα : 0 < α) : cstar typ hα ∉ CuK typ 0 := by
  rw [mem_CuK]
  rcases hf : firstA typ with _ | b
  · rw [cstar_none typ hα hf]
    have := firstA_none typ hf ⟨0, hα⟩
    simp [meets, this, metPos]
    decide
  · rw [cstar_some typ hα hf]
    have := firstA_some typ hf
    simp [meets, this, metPos]
    decide

/-- In each block at most one copy of `CuK 0` shares a barred class with the missed copy. The missed
copy lies in a block of type a at position 3, or (when every block has type b) in a block of type b at
position 0. -/
theorem unique_star : ∀ ty ty' : Bool, ∀ j : ZMod 5,
    ((ty' = false ∧ j = 3) ∨ (ty' = true ∧ j = 0 ∧ ty = true)) →
    ∀ i₁ i₂ : ZMod 5,
      (metPos ty false 0 i₁ = true ∧ ∃ k, metPos ty true k i₁ = true ∧ metPos ty' true k j = true) →
      (metPos ty false 0 i₂ = true ∧ ∃ k, metPos ty true k i₂ = true ∧ metPos ty' true k j = true) →
      i₁ = i₂ := by
  decide

/-- **Lemma 3.2.** For the missed copy `c'` of `cstar`, `|F0| ≤ α`: one copy per block. -/
theorem card_F0_le (hα : 0 < α) : (F0 typ 0 (cstar typ hα)).card ≤ α := by
  have hinj : Set.InjOn Prod.fst (F0 typ 0 (cstar typ hα) : Set (Copy α)) := by
    rintro ⟨b, i₁⟩ h1 ⟨b', i₂⟩ h2 hb
    simp only at hb
    subst hb
    rw [Finset.mem_coe, mem_F0] at h1 h2
    have key : ∀ (c' : Copy α) (i : ZMod 5), meets typ false 0 (b, i) = true → share typ true (b, i) c' = true →
        (metPos (typ b) false 0 i = true ∧ ∃ k, metPos (typ b) true k i = true ∧ metPos (typ c'.1) true k c'.2 = true) := by
      intro c' i hm hs
      refine ⟨hm, ?_⟩
      simp only [share, Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨_, k, hk1, hk2⟩ := hs
      exact ⟨k, hk1, hk2⟩
    have hcs : (typ (cstar typ hα).1 = false ∧ (cstar typ hα).2 = 3) ∨
        (typ (cstar typ hα).1 = true ∧ (cstar typ hα).2 = 0 ∧ typ b = true) := by
      rcases hf : firstA typ with _ | b0
      · right
        rw [cstar_none typ hα hf]
        exact ⟨firstA_none typ hf _, rfl, firstA_none typ hf b⟩
      · left
        rw [cstar_some typ hα hf]
        exact ⟨firstA_some typ hf, rfl⟩
    have p1 := key _ i₁ h1.1 h1.2
    have p2 := key _ i₂ h2.1 h2.2
    have hu := unique_star (typ b) (typ (cstar typ hα).1) (cstar typ hα).2 hcs i₁ i₂ p1 p2
    rw [hu]
  calc (F0 typ 0 (cstar typ hα)).card ≤ (Finset.univ : Finset (Fin α)).card :=
        Finset.card_le_card_of_injOn Prod.fst (fun _ _ => Finset.mem_univ _) hinj
    _ = α := by simp


/-! ### Crude counts (for `q ≥ 10`) -/

theorem card_F1_le (k : ZMod 5) (c' : Copy α) : (F1 typ k c').card ≤ 4 * α := by
  have hsub : F1 typ k c' ⊆ (univ : Finset (Copy α)).filter fun x => share typ true c' x = true := by
    intro x hx
    simp only [F1, Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [share_comm]; exact hx.2
  exact (Finset.card_le_card hsub).trans (card_share_le typ true c')

theorem card_F2_le (k : ZMod 5) (c' : Copy α) : (F2 typ k c').card ≤ 2 * α * (4 * α) := by
  have hsub : F2 typ k c' ⊆ (CuK typ k).biUnion fun c₁ =>
      ((univ : Finset (Copy α)).filter fun x => share typ true c₁ x = true).image fun x => (c₁, x) := by
    intro p hp
    simp only [F2, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, Bool.and_eq_true] at hp
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨h1, h2, _⟩ := hp
    exact ⟨p.1, h1, p.2, h2, rfl⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ c₁ ∈ CuK typ k, (((univ : Finset (Copy α)).filter fun x => share typ true c₁ x = true).image
        fun x => (c₁, x)).card ≤ ∑ c₁ ∈ CuK typ k, 4 * α := by
        refine Finset.sum_le_sum fun c₁ _ => ?_
        refine Finset.card_image_le.trans (card_share_le typ true c₁)
    _ = 2 * α * (4 * α) := by rw [Finset.sum_const, card_CuK]; simp

theorem card_F3_sdiff (k : ZMod 5) (c' : Copy α) :
    (F3 typ k c' \ F0 typ k c').card + (F0 typ k c').card ≤ 2 * α := by
  have h1 : F3 typ k c' \ F0 typ k c' ⊆ CuK typ k \ F0 typ k c' :=
    Finset.sdiff_subset_sdiff (F3_subset typ k c') (le_refl _)
  have h2 := Finset.card_le_card h1
  rw [Finset.card_sdiff_of_subset (F0_subset typ k c'), card_CuK] at h2
  have h3 := Finset.card_le_card (F0_subset typ k c')
  rw [card_CuK] at h3
  omega

theorem m2_add_le (k : ZMod 5) (c' : Copy α) : m2 typ k c' + (F0 typ k c').card ≤ 8 * α ^ 2 + 6 * α := by
  have := card_F1_le typ k c'
  have := card_F2_le typ k c'
  have := card_F3_sdiff typ k c'
  unfold m2
  nlinarith

/-- The arithmetic of Theorem 3.3 for `q ≥ 10`. -/
theorem crude_ineq {q : ℕ} (hq : 10 ≤ q) (h2 : 2 * α ≤ q + 3) :
    α * (q ^ 4 + q ^ 2) + (8 * α ^ 2 + 6 * α) * q ^ 2 < q ^ 5 := by
  by_cases h10 : q = 10
  · subst h10
    have : α ≤ 6 := by omega
    interval_cases α <;> norm_num
  · have hq11 : 11 ≤ q := by omega
    -- `4 (q⁵ - α q⁴ - (8 α² + 7 α) q²) ≥ …`; use `2 α ≤ q + 3`
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 11 := ⟨q - 11, by omega⟩
    nlinarith [Nat.mul_le_mul_left (q' + 11) h2, Nat.mul_le_mul h2 h2, pow_pos (show 0 < q' + 11 by omega) 2,
      pow_pos (show 0 < q' + 11 by omega) 3, pow_pos (show 0 < q' + 11 by omega) 4]

theorem star_crude {q : ℕ} (hα : 0 < α) (hq : 10 ≤ q) (h2 : 2 * α ≤ q + 3) :
    (F0 typ 0 (cstar typ hα)).card * (q ^ 4 + 2 * q ^ 2) + m2 typ 0 (cstar typ hα) * q ^ 2 < q ^ 5 := by
  have h0 := card_F0_le typ hα
  have hm := m2_add_le typ 0 (cstar typ hα)
  have hc := crude_ineq (α := α) hq h2
  set n := (F0 typ 0 (cstar typ hα)).card
  set m := m2 typ 0 (cstar typ hα)
  have h3 : n * (q ^ 4 + 2 * q ^ 2) + m * q ^ 2 = n * (q ^ 4 + q ^ 2) + (m + n) * q ^ 2 := by ring
  rw [h3]
  have h4 : n * (q ^ 4 + q ^ 2) ≤ α * (q ^ 4 + q ^ 2) := Nat.mul_le_mul_right _ h0
  have h5 : (m + n) * q ^ 2 ≤ (8 * α ^ 2 + 6 * α) * q ^ 2 := Nat.mul_le_mul_right _ hm
  omega

end BipartiteDD.LeanMaxx.Omega3
