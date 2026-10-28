import BipartiteDD.LeanMaxx.Omega3.Main
import BipartiteDD.LeanMaxx.Omega45.Exact

/-!
# A far pair from a bound on the radius-4 part of the cover

`Omega3/Main.lean` covers the vertices of a missed copy `c'` that are within distance `7` of the hub `(0, t)`
by the balls of `covSet`: the radius-4 balls around the centres `cen lam t c₁ c'`, `c₁ ∈ F0 typ 0 c'`
(`rad4`), and `m2 typ 0 c'` balls of radius `2`. Here the radius-4 part is kept as a set, so that the
overlaps of the balls (Bonferroni, Lemma 4.3 of the note) and coincidences of centres (Lemma 4.2) can be
used instead of the crude sum.

* `far_of_rad4`: if `|rad4| + m2 q² < q⁵` then `ΩH_q` has a pair of vertices (the hub `(0, t)` and a vertex of
  `c'`) at distance `≥ 9`. This is the argument of `omega3_far` with the counting hypothesis replaced by one
  about the set `rad4`.
* `far_of_centres` (Lemma 4.2 in general form): if the radius-4 centres other than `t` are at most `n`
  points and `n q⁴ + m q² < q⁵` for `m2 ≤ m`, then there is a far pair. Uses the exact constant
  of `Exact.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace BipartiteDD.LeanMaxx.Omega45

open Finset BipartiteDD.LeanMaxx.Omega2 BipartiteDD.LeanMaxx.Omega3

variable {β : Type*} [Fintype β] [DecidableEq β] {B : SimpleGraph β} [DecidableRel B.Adj]
  {κ : β → ZMod 2} {q α : ℕ}

/-- The radius-4 centres of the hub row `t` towards the missed copy `c'`. -/
def cen4 (typ : Fin α → Bool) (lam : Copy α → Equiv.Perm β) (t : β) (c' : Copy α) : Finset β :=
  (F0 typ 0 c').image fun c₁ => cen lam t c₁ c'

/-- The vertices opposite `t` covered by the radius-4 balls. -/
noncomputable def rad4 (B : SimpleGraph β) (typ : Fin α → Bool) (lam : Copy α → Equiv.Perm β) (t : β)
    (c' : Copy α) : Finset β :=
  (F0 typ 0 c').biUnion (fun c₁ => ballOpp B t (cen lam t c₁ c') 4)

theorem rad4_eq (typ : Fin α → Bool) (lam : Copy α → Equiv.Perm β) (t : β) (c' : Copy α) :
    rad4 B typ lam t c' = (cen4 typ lam t c').biUnion (fun y => ballOpp B t y 4) := by
  unfold rad4 cen4
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨c₁, h1, h2⟩; exact ⟨_, ⟨c₁, h1, rfl⟩, h2⟩
  · rintro ⟨y, ⟨c₁, h1, rfl⟩, h2⟩; exact ⟨c₁, h1, h2⟩

theorem ballOpp_self (H : Hex B κ q) (t : β) (r : ℕ) (hr : r ≤ 5) : ballOpp B t t r = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_ballOpp] at hx
  have := dist_tri H t t x
  simp at this
  omega

/-- Dropping the hub row from the centres. -/
theorem rad4_eq_erase (H : Hex B κ q) (typ : Fin α → Bool) (lam : Copy α → Equiv.Perm β) (t : β)
    (c' : Copy α) :
    rad4 B typ lam t c' = ((cen4 typ lam t c').erase t).biUnion (fun y => ballOpp B t y 4) := by
  rw [rad4_eq]
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_erase]
  constructor
  · rintro ⟨y, hy, hx⟩
    refine ⟨y, ⟨?_, hy⟩, hx⟩
    rintro rfl
    rw [ballOpp_self H y 4 (by omega)] at hx
    simp at hx
  · rintro ⟨y, ⟨_, hy⟩, hx⟩
    exact ⟨y, hy, hx⟩

/-- The radius-2 centres as words: `cenW lam t a b = λ_a λ_b⁻¹ (t)`, so `cen lam t c d = cenW lam t d c`. -/
def cenW (lam : Copy α → Equiv.Perm β) (t : β) (a b : Copy α) : β := (lam a * (lam b)⁻¹) t

theorem cen_eq_cenW (lam : Copy α → Equiv.Perm β) (t : β) (c d : Copy α) : cen lam t c d = cenW lam t d c := rfl

theorem cenW_self (lam : Copy α → Equiv.Perm β) (t : β) (a : Copy α) : cenW lam t a a = t := by
  simp [cenW]

/-- The distinct words `(a, b)` of radius-2 centres `λ_a λ_b⁻¹ (t)`, coming from `F1`, `F2` and `F3 \ F0`. -/
def Dall (typ : Fin α → Bool) (c' : Copy α) : Finset (Copy α × Copy α) :=
  (F1 typ 0 c').image (fun x => (c', x)) ∪ (F2 typ 0 c').image (fun p => (p.2, p.1)) ∪
    ((F3 typ 0 c' \ F0 typ 0 c').image fun c₁ => (c', c₁))

/-- The radius-2 words that matter: not the identity word (centre `t`, empty ball) and not a radius-4 centre
(its radius-2 ball lies in the radius-4 ball). -/
def D2 (typ : Fin α → Bool) (c' : Copy α) : Finset (Copy α × Copy α) :=
  (Dall typ c').filter fun p => p.1 ≠ p.2 ∧ ¬ (p.1 = c' ∧ p.2 ∈ F0 typ 0 c')

/-- The vertices opposite `t` covered by the radius-2 balls of `D2`. -/
noncomputable def rad2 (B : SimpleGraph β) (typ : Fin α → Bool) (lam : Copy α → Equiv.Perm β) (t : β)
    (c' : Copy α) : Finset β :=
  (D2 typ c').biUnion (fun p => ballOpp B t (cenW lam t p.1 p.2) 2)

theorem covSet_subset (H : Hex B κ q) (typ : Fin α → Bool) (lam : Copy α → Equiv.Perm β) (t : β)
    (c' : Copy α) : covSet B typ lam t c' ⊆ rad4 B typ lam t c' ∪ rad2 B typ lam t c' := by
  intro y hy
  have hself : ∀ r, r ≤ 5 → y ∉ ballOpp B t t r := fun r hr h => by
    rw [ballOpp_self H t r hr] at h; simp at h
  -- a radius-2 ball around a radius-4 centre lies in `rad4`
  have h24 : ∀ c₁ ∈ F0 typ 0 c', y ∈ ballOpp B t (cen lam t c₁ c') 2 → y ∈ rad4 B typ lam t c' := by
    intro c₁ hc₁ hmem
    unfold rad4
    exact Finset.mem_biUnion.2 ⟨c₁, hc₁, ballOpp_mono (by omega) hmem⟩
  have hD : ∀ a b, (a, b) ∈ Dall typ c' → y ∈ ballOpp B t (cenW lam t a b) 2 →
      y ∈ rad4 B typ lam t c' ∪ rad2 B typ lam t c' := by
    intro a b hab hmem
    by_cases h1 : a = b
    · subst h1
      rw [cenW_self] at hmem
      exact absurd hmem (hself 2 (by omega))
    · by_cases h2 : a = c' ∧ b ∈ F0 typ 0 c'
      · obtain ⟨rfl, hb⟩ := h2
        exact Finset.mem_union_left _ (h24 b hb hmem)
      · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨(a, b), ?_, hmem⟩)
        exact Finset.mem_filter.2 ⟨hab, h1, h2⟩
  unfold covSet at hy
  simp only [Finset.mem_union, Finset.mem_biUnion] at hy
  rcases hy with ((⟨c₁, h1, h2⟩ | ⟨x, h1, h2⟩) | ⟨p, h1, h2⟩) | ⟨c₁, h1, h2⟩
  · refine Finset.mem_union_left _ ?_
    unfold rad4
    exact Finset.mem_biUnion.2 ⟨c₁, h1, h2⟩
  · exact hD c' x (by unfold Dall; simp only [Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl ⟨x, h1, rfl⟩)) h2
  · exact hD p.2 p.1 (by unfold Dall; simp only [Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inr ⟨p, h1, rfl⟩)) h2
  · exact hD c' c₁ (by unfold Dall; simp only [Finset.mem_union, Finset.mem_image]; exact Or.inr ⟨c₁, h1, rfl⟩) h2

theorem card_rad2_le (H : Hex B κ q) (hq : 1 ≤ q) (typ : Fin α → Bool) (lam : Copy α → autSub B κ)
    (t : β) (c' : Copy α) :
    (rad2 B typ (fun c => (lam c : Equiv.Perm β)) t c').card ≤ (D2 typ c').card * q ^ 2 := by
  refine (Finset.card_biUnion_le).trans (Finset.sum_le_card_nsmul _ _ _ fun p _ => ?_)
  exact card_ballOpp_two_le H hq (col_cen lam t p.2 p.1)

theorem card_covSet_le_rad4 (H : Hex B κ q) (hq : 1 ≤ q) (typ : Fin α → Bool) (lam : Copy α → autSub B κ)
    (t : β) (c' : Copy α) :
    (covSet B typ (fun c => (lam c : Equiv.Perm β)) t c').card ≤
      (rad4 B typ (fun c => (lam c : Equiv.Perm β)) t c').card + (D2 typ c').card * q ^ 2 :=
  ((Finset.card_le_card (covSet_subset H typ _ t c')).trans (Finset.card_union_le _ _)).trans
    (Nat.add_le_add_left (card_rad2_le H hq typ lam t c') _)

/-- **A far pair from a bound on `rad4`.** `t` is a row of colour `ε₀`, `c'` a copy missed by the unbarred
class `0`, and the radius-4 balls together with the the radius-2 balls of `D2` cover fewer than `q⁵` of the
vertices opposite `t`. Then the hub `(0, t)` and some vertex of `c'` are at distance `≥ 9`. -/
theorem far_of_rad4 [Nonempty β] (H : Hex B κ q) (hq : 1 ≤ q) {typ : Fin α → Bool} {ε₀ : ZMod 2}
    (lam : Copy α → autSub B κ) {t : β} (ht : κ t = ε₀) {c' : Copy α} (hc'not : c' ∉ CuK typ 0)
    (hnum : (rad4 B typ (fun c => (lam c : Equiv.Perm β)) t c').card + (D2 typ c').card * q ^ 2 < q ^ 5) :
    ∃ x y, (9 : ℕ∞) ≤ (omega B κ typ ε₀ (nfmk (fun c => (lam c : Equiv.Perm β)))).edist x y := by
  set mk := nfmk (fun c => (lam c : Equiv.Perm β)) with hmk
  have hcard : (covSet B typ (fun c => (lam c : Equiv.Perm β)) t c').card < (opp B t).card := by
    have h1 := card_covSet_le_rad4 H hq typ lam t c'
    have h2' := q_pow_five_le_card_sph_six H.col H.deg H.girth H.reach (u := t) hq
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le hnum h2')
  obtain ⟨y', hy'opp, hy'not⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hy6 : B.dist t y' = 6 := mem_opp.1 hy'opp
  set h : Hub κ ε₀ := ⟨false, 0, t, by simpa using ht⟩ with hh
  have key : ∀ W : (omega B κ typ ε₀ mk).Walk (Sum.inr h) (Sum.inl (c', y')), 9 ≤ W.length := by
    intro W
    by_contra hlt
    have hlt' : W.length < 9 := Nat.lt_of_not_le hlt
    have hpar := col_walk (fun a b hab => Kcol_proper H.col (nfmk_col lam) hab) W
    have hKv : Kcol (α := α) (κ := κ) (ε₀ := ε₀) (Sum.inl (c', y')) = ε₀ := by
      simp only [Kcol, Sum.elim_inl]
      rw [← col_opp H hy6, ht]
    have hKh : Kcol (α := α) (κ := κ) (ε₀ := ε₀) (Sum.inr h) = ε₀ + 1 := by
      simp only [Kcol, Sum.elim_inr, hh]; rw [ht]
    rw [hKv, hKh] at hpar
    have hodd : (W.length : ZMod 2) = 1 := zmod2_aux ε₀ _ hpar
    obtain ⟨m, hm⟩ := (ZMod.natCast_eq_one_iff_odd.1 hodd)
    have hle : W.length ≤ 7 := by omega
    cases W with
    | @cons _ x _ hadj W' =>
      rcases x with ⟨c₁, y₁⟩ | h₂
      · rw [omega_adj_hc] at hadj
        obtain ⟨hmeet, hy₁⟩ := hadj
        have hy₁t : y₁ = t := by rw [hy₁]; simp [hmk, nfmk, hh]
        subst hy₁t
        have hlen : W'.length ≤ 6 := by simp at hle; omega
        obtain ⟨fn, a, hr, ha, wB, hwB⟩ :=
          walk_route H.col (nfmk_col lam) (nfmk_mem lam) _ c₁ _ c' y' W' rfl
        have hshape := shape (typ := typ) (lam := fun c => (lam c : Equiv.Perm β)) (ε₀ := ε₀)
          ((mem_CuK typ).2 hmeet) hc'not (by rwa [ht] at hr) (by omega) ⟨wB, hwB⟩ (by omega)
        exact hy'not (mem_covSet hy6 hshape)
      · exact absurd hadj not_omega_adj_hh
  have hedist : (9 : ℕ∞) ≤ (omega B κ typ ε₀ mk).edist (Sum.inr h) (Sum.inl (c', y')) := by
    unfold SimpleGraph.edist
    refine le_iInf fun W => ?_
    exact_mod_cast key W
  exact ⟨_, _, hedist⟩

/-- `|rad4| ≤ n q⁴` when at most `n` radius-4 centres differ from `t` (exact Lemma 3.1). -/
theorem card_rad4_le (H : Hex B κ q) (hq : 1 ≤ q) (typ : Fin α → Bool) (lam : Copy α → autSub B κ)
    (t : β) (c' : Copy α) :
    (rad4 B typ (fun c => (lam c : Equiv.Perm β)) t c').card ≤
      ((cen4 typ (fun c => (lam c : Equiv.Perm β)) t c').erase t).card * q ^ 4 := by
  rw [rad4_eq_erase H]
  refine (Finset.card_biUnion_le).trans (Finset.sum_le_card_nsmul _ _ _ fun y hy => ?_)
  have hy' : κ y = κ t := by
    obtain ⟨_, hy2⟩ := Finset.mem_erase.1 hy
    obtain ⟨c₁, _, rfl⟩ := Finset.mem_image.1 hy2
    exact col_cen lam t c₁ c'
  exact card_ballOpp_four_le_exact H hq hy'

/-- **Lemma 4.2, general form.** If at most `n` points other than `t` are radius-4 centres, `m2 ≤ m`, and
`n q⁴ + m q² < q⁵`, then `ΩH_q` has a far pair (the hub `(0, t)` and a vertex of the missed copy). -/
theorem far_of_centres [Nonempty β] (H : Hex B κ q) (hq : 1 ≤ q) {typ : Fin α → Bool} {ε₀ : ZMod 2}
    (lam : Copy α → autSub B κ) {t : β} (ht : κ t = ε₀) {c' : Copy α} (hc'not : c' ∉ CuK typ 0)
    {n m : ℕ} (hn : ((cen4 typ (fun c => (lam c : Equiv.Perm β)) t c').erase t).card ≤ n)
    (hm : (D2 typ c').card ≤ m) (hnum : n * q ^ 4 + m * q ^ 2 < q ^ 5) :
    ∃ x y, (9 : ℕ∞) ≤ (omega B κ typ ε₀ (nfmk (fun c => (lam c : Equiv.Perm β)))).edist x y := by
  refine far_of_rad4 H hq lam ht hc'not ?_
  have h1 := card_rad4_le H hq typ lam t c'
  have h2 : ((cen4 typ (fun c => (lam c : Equiv.Perm β)) t c').erase t).card * q ^ 4 ≤ n * q ^ 4 :=
    Nat.mul_le_mul_right _ hn
  have h3 : (D2 typ c').card * q ^ 2 ≤ m * q ^ 2 := Nat.mul_le_mul_right _ hm
  omega

end BipartiteDD.LeanMaxx.Omega45
