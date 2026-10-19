import Mathlib

namespace BipartiteDD.SingerC

open Classical

section QuadCount

variable {F : Type*} [Field F] [Fintype F]

omit [Fintype F] in
lemma two_ne_zero_of_ringChar_ne_two (hF : ringChar F ≠ 2) : (2 : F) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  have hd : ringChar F ∣ 2 := (CharP.cast_eq_zero_iff F (ringChar F) 2).mp h'
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · exact hF h1

/-- Number of roots of `a s^2 + b s + c` for `a ≠ 0`. -/
lemma root_count (hF : ringChar F ≠ 2) (a b c : F) (ha : a ≠ 0) :
    ((Finset.univ.filter (fun s : F => a * s ^ 2 + b * s + c = 0)).card : ℤ)
      = quadraticChar F (b ^ 2 - 4 * a * c) + 1 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_ringChar_ne_two hF
  have h2a : (2 : F) * a ≠ 0 := mul_ne_zero h2 ha
  have h4a : (4 : F) * a ≠ 0 := by
    have h4 : (4 : F) = 2 * 2 := by norm_num
    rw [h4]
    exact mul_ne_zero (mul_ne_zero h2 h2) ha
  have key : (Finset.univ.filter (fun s : F => a * s ^ 2 + b * s + c = 0)).card
      = (Finset.univ.filter (fun r : F => r ^ 2 = b ^ 2 - 4 * a * c)).card := by
    apply Finset.card_nbij' (fun s => 2 * a * s + b) (fun r => (r - b) / (2 * a))
    · intro s hs
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      linear_combination (4 * a) * hs
    · intro r hr
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      have hs : 2 * a * ((r - b) / (2 * a)) = r - b := by field_simp
      have h4 : (4 * a) * (a * ((r - b) / (2 * a)) ^ 2 + b * ((r - b) / (2 * a)) + c) = 0 := by
        linear_combination (2 * a * ((r - b) / (2 * a)) + b + r) * hs + hr
      rcases mul_eq_zero.mp h4 with h | h
      · exact absurd h h4a
      · exact h
    · intro s _
      dsimp only
      rw [add_sub_cancel_right, mul_div_cancel_left₀ s h2a]
    · intro r _
      dsimp only
      have hs : 2 * a * ((r - b) / (2 * a)) = r - b := by field_simp
      rw [hs]
      ring
  rw [key]
  have hq := quadraticChar_card_sqrts hF (b ^ 2 - 4 * a * c)
  rw [Set.toFinset_ofPred] at hq
  exact_mod_cast hq

omit [Field F] in
/-- Counting over `F × F` by fibres over the second coordinate. -/
lemma card_filter_prod_eq_sum (P : F × F → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card
      = ∑ t : F, (Finset.univ.filter (fun s : F => P (s, t))).card := by
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.card_filter]

omit [Field F] in
/-- Swapping coordinates preserves the count. -/
lemma card_filter_congr_swap (P Q : F × F → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ st, P st ↔ Q st.swap) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card := by
  apply Finset.card_nbij' Prod.swap Prod.swap
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact (h x).mp hx
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact (h x.swap).mpr (by simpa using hx)
  · intro x _
    simp
  · intro x _
    simp

/-- Zeros of the form when `α ≠ 0`, including `(0,0)`. -/
lemma zeros_count_of_ne (hF : ringChar F ≠ 2) (α β γ : F) (hα : α ≠ 0) :
    ((Finset.univ.filter (fun st : F × F =>
        α * st.1 ^ 2 + β * st.1 * st.2 + γ * st.2 ^ 2 = 0)).card : ℤ)
      = ((Fintype.card F : ℤ) - 1) * (1 + quadraticChar F (β ^ 2 - 4 * α * γ)) + 1 := by
  rw [card_filter_prod_eq_sum]
  push_cast
  have hinner : ∀ t : F, (Finset.univ.filter (fun s : F =>
      α * s ^ 2 + β * s * t + γ * t ^ 2 = 0))
        = Finset.univ.filter (fun s : F => α * s ^ 2 + (β * t) * s + γ * t ^ 2 = 0) := by
    intro t
    apply Finset.filter_congr
    intro s _
    rw [show β * s * t = β * t * s by ring]
  have hsum : ∀ t : F, ((Finset.univ.filter (fun s : F =>
      α * s ^ 2 + β * s * t + γ * t ^ 2 = 0)).card : ℤ)
        = quadraticChar F (β ^ 2 - 4 * α * γ) + 1
          - (if t = 0 then quadraticChar F (β ^ 2 - 4 * α * γ) else 0) := by
    intro t
    rw [hinner t, root_count hF α (β * t) (γ * t ^ 2) hα]
    by_cases ht : t = 0
    · subst ht
      simp
    · have e : (β * t) ^ 2 - 4 * α * (γ * t ^ 2) = t ^ 2 * (β ^ 2 - 4 * α * γ) := by ring
      rw [e, map_mul, quadraticChar_sq_one' ht, one_mul]
      simp [ht]
  rw [Finset.sum_congr rfl (fun t _ => hsum t)]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']
  ring

/-- Zeros of the form when `α = 0`, `γ ≠ 0`: swap the coordinates. -/
lemma zeros_count_of_ne_right (hF : ringChar F ≠ 2) (β γ : F) (hγ : γ ≠ 0) :
    ((Finset.univ.filter (fun st : F × F =>
        0 * st.1 ^ 2 + β * st.1 * st.2 + γ * st.2 ^ 2 = 0)).card : ℤ)
      = ((Fintype.card F : ℤ) - 1) * (1 + quadraticChar F (β ^ 2 - 4 * 0 * γ)) + 1 := by
  have hswap := card_filter_congr_swap
    (fun st : F × F => 0 * st.1 ^ 2 + β * st.1 * st.2 + γ * st.2 ^ 2 = 0)
    (fun st : F × F => γ * st.1 ^ 2 + β * st.1 * st.2 + 0 * st.2 ^ 2 = 0)
    (fun st => by
      simp only [Prod.fst_swap, Prod.snd_swap]
      constructor <;> intro h <;> linear_combination h)
  rw [hswap, zeros_count_of_ne hF γ β 0 hγ]
  simp

/-- The case `α = γ = 0`, `β ≠ 0`. -/
lemma zeros_count_zero (β : F) (hβ : β ≠ 0) :
    ((Finset.univ.filter (fun st : F × F =>
        0 * st.1 ^ 2 + β * st.1 * st.2 + 0 * st.2 ^ 2 = 0)).card : ℤ)
      = ((Fintype.card F : ℤ) - 1) * (1 + quadraticChar F (β ^ 2 - 4 * 0 * 0)) + 1 := by
  have hχ : quadraticChar F (β ^ 2 - 4 * 0 * 0) = 1 := by
    rw [show β ^ 2 - 4 * 0 * 0 = β ^ 2 by ring]
    exact quadraticChar_sq_one' hβ
  rw [hχ, card_filter_prod_eq_sum]
  push_cast
  have hinner : ∀ t : F, ((Finset.univ.filter (fun s : F =>
      0 * s ^ 2 + β * s * t + 0 * t ^ 2 = 0)).card : ℤ)
        = 1 + (if t = 0 then ((Fintype.card F : ℤ) - 1) else 0) := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simp
    · have : Finset.univ.filter (fun s : F => 0 * s ^ 2 + β * s * t + 0 * t ^ 2 = 0)
          = {0} := by
        ext s
        simp [hβ, ht]
      rw [this]
      simp [ht]
  rw [Finset.sum_congr rfl (fun t _ => hinner t)]
  rw [Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']
  ring

theorem card_zeros_form {F : Type*} [Field F] [Fintype F] (hF : ringChar F ≠ 2) (α β γ : F)
    (h : ¬ (α = 0 ∧ β = 0 ∧ γ = 0)) :
    ((Finset.univ.filter (fun st : F × F =>
        st ≠ 0 ∧ α * st.1 ^ 2 + β * st.1 * st.2 + γ * st.2 ^ 2 = 0)).card : ℤ)
      = ((Fintype.card F : ℤ) - 1) * (1 + quadraticChar F (β ^ 2 - 4 * α * γ)) := by
  -- the nonzero zeros are the zeros of the form minus the origin
  have hfilt : (Finset.univ.filter (fun st : F × F =>
      st ≠ 0 ∧ α * st.1 ^ 2 + β * st.1 * st.2 + γ * st.2 ^ 2 = 0))
      = (Finset.univ.filter (fun st : F × F =>
          α * st.1 ^ 2 + β * st.1 * st.2 + γ * st.2 ^ 2 = 0)).erase 0 := by
    ext st
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  have h0 : (0 : F × F) ∈ Finset.univ.filter (fun st : F × F =>
      α * st.1 ^ 2 + β * st.1 * st.2 + γ * st.2 ^ 2 = 0) := by
    simp
  have hpos : 0 < (Finset.univ.filter (fun st : F × F =>
      α * st.1 ^ 2 + β * st.1 * st.2 + γ * st.2 ^ 2 = 0)).card :=
    Finset.card_pos.mpr ⟨0, h0⟩
  rw [hfilt, Finset.card_erase_of_mem h0, Nat.cast_pred hpos]
  have hN : ((Finset.univ.filter (fun st : F × F =>
      α * st.1 ^ 2 + β * st.1 * st.2 + γ * st.2 ^ 2 = 0)).card : ℤ)
      = ((Fintype.card F : ℤ) - 1) * (1 + quadraticChar F (β ^ 2 - 4 * α * γ)) + 1 := by
    by_cases hα : α = 0
    · subst hα
      by_cases hγ : γ = 0
      · subst hγ
        have hβ : β ≠ 0 := by
          intro hβ
          exact h ⟨rfl, hβ, rfl⟩
        exact zeros_count_zero β hβ
      · exact zeros_count_of_ne_right hF β γ hγ
    · exact zeros_count_of_ne hF α β γ hα
  rw [hN]
  ring

end QuadCount

end BipartiteDD.SingerC
