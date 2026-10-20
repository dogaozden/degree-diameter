import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Group GQST, part 6: an explicit biregular bipartite relation between two finite sides.

Given `a A b B` with `a * A = b * B` and `A ≤ b`, the relation `biRel a b A` on `ℕ` is realised by
`z ↦ (z / A, z % b)` on `[0, a * A)`. Each `i < a` has exactly `A` partners `j < b`, and each `j < b`
has exactly `B` partners `i < a`. No pair is produced twice, so the counts are exact. -/

namespace BipartiteDD.GQST

/-- `i ~ j` when some `z < a * A` has `z / A = i` and `z % b = j`. -/
def biRel (a b A : ℕ) (i j : ℕ) : Prop :=
  ∃ z, z < a * A ∧ z / A = i ∧ z % b = j

theorem mod_inj_of_lt {A b k k' i : ℕ} (hk : k < A) (hk' : k' < A) (hAb : A ≤ b)
    (h : (i * A + k) % b = (i * A + k') % b) : k = k' := by
  have h2 : k ≡ k' [MOD b] := Nat.ModEq.add_left_cancel' (i * A) h
  unfold Nat.ModEq at h2
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2

theorem div_inj_of_lt {A b j t t' : ℕ} (hApos : 0 < A) (hAb : A ≤ b)
    (h : (j + b * t) / A = (j + b * t') / A) : t = t' := by
  have e1 := Nat.div_add_mod (j + b * t) A
  have e2 := Nat.div_add_mod (j + b * t') A
  have r1 := Nat.mod_lt (j + b * t) hApos
  have r2 := Nat.mod_lt (j + b * t') hApos
  rw [h] at e1
  rcases lt_trichotomy t t' with hlt | rfl | hgt
  · have h3 : b * (t + 1) ≤ b * t' := Nat.mul_le_mul_left b hlt
    have h4 : b * (t + 1) = b * t + b := by ring
    omega
  · rfl
  · have h3 : b * (t' + 1) ≤ b * t := Nat.mul_le_mul_left b hgt
    have h4 : b * (t' + 1) = b * t' + b := by ring
    omega

theorem biregular_exists (a b A B : ℕ) (h : a * A = b * B) (hA : 0 < a → A ≤ b) :
    ∃ R : Fin a → Fin b → Prop, (∀ i, Nat.card {j // R i j} = A) ∧
      (∀ j, Nat.card {i // R i j} = B) := by
  rcases Nat.eq_zero_or_pos A with rfl | hApos
  · -- no partners on the `a`-side; the `b`-side is empty unless `B = 0`
    have hR : ∀ i j, ¬ biRel a b 0 i j := by
      rintro i j ⟨z, hz, -⟩
      simp at hz
    refine ⟨fun i j => biRel a b 0 i j, fun i => ?_, fun j => ?_⟩
    · simp [hR]
    · have hb : 0 < b := by have := j.isLt; omega
      have hB : B = 0 := by
        simp only [mul_zero] at h
        rcases Nat.mul_eq_zero.mp h.symm with h0 | h0
        · omega
        · exact h0
      simp [hR, hB]
  · refine ⟨fun i j => biRel a b A i j, fun i => ?_, fun j => ?_⟩
    · have hAb : A ≤ b := hA (lt_of_le_of_lt (Nat.zero_le _) i.isLt)
      have hbpos : 0 < b := by omega
      have hz : ∀ k : Fin A, (i : ℕ) * A + k < a * A := fun k => by
        have h1 : ((i : ℕ) + 1) * A ≤ a * A := Nat.mul_le_mul_right A i.isLt
        have h2 := k.isLt
        rw [Nat.succ_mul] at h1
        omega
      have hq : ∀ k : Fin A, ((i : ℕ) * A + k) / A = i := fun k => by
        rw [Nat.mul_comm (i : ℕ) A, Nat.mul_add_div hApos, Nat.div_eq_of_lt k.isLt, add_zero]
      have hf : Function.Bijective (fun k : Fin A =>
          (⟨⟨((i : ℕ) * A + k) % b, Nat.mod_lt _ hbpos⟩,
            ⟨(i : ℕ) * A + k, hz k, hq k, rfl⟩⟩ : {j : Fin b // biRel a b A i j})) := by
        constructor
        · intro k k' hkk
          have := congrArg (fun x : {j : Fin b // biRel a b A i j} => (x.1 : ℕ)) hkk
          simp only at this
          exact Fin.ext (mod_inj_of_lt k.isLt k'.isLt hAb this)
        · rintro ⟨j, z, hzlt, hzi, hzj⟩
          refine ⟨⟨z % A, Nat.mod_lt _ hApos⟩, ?_⟩
          apply Subtype.ext
          apply Fin.ext
          have e := Nat.div_add_mod z A
          rw [hzi, Nat.mul_comm] at e
          simp only
          rw [e, hzj]
      have := Nat.card_eq_of_bijective _ hf
      rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
      exact this.symm
    · have hb : 0 < b := by have := j.isLt; omega
      rcases Nat.eq_zero_or_pos a with ha | ha
      · -- `a = 0` forces `B = 0`, and the count is over the empty type `Fin 0`
        subst ha
        have hB : B = 0 := by
          simp only [zero_mul] at h
          rcases Nat.mul_eq_zero.mp h.symm with h0 | h0
          · omega
          · exact h0
        subst hB
        simp
      have hAb : A ≤ b := hA ha
      have hBt : ∀ t : Fin B, j + b * (t : ℕ) < a * A := fun t => by
        have h1 : b * ((t : ℕ) + 1) ≤ b * B := Nat.mul_le_mul_left b t.isLt
        have h2 : b * ((t : ℕ) + 1) = b * t + b := by ring
        have h3 := j.isLt
        omega
      have hf : Function.Bijective (fun t : Fin B =>
          (⟨⟨((j : ℕ) + b * t) / A, (Nat.div_lt_iff_lt_mul hApos).2 (hBt t)⟩,
            ⟨(j : ℕ) + b * t, hBt t, rfl, by
              rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]⟩⟩ :
              {i : Fin a // biRel a b A i j})) := by
        constructor
        · intro t t' htt
          have := congrArg (fun x : {i : Fin a // biRel a b A i j} => (x.1 : ℕ)) htt
          simp only at this
          exact Fin.ext (div_inj_of_lt hApos hAb this)
        · rintro ⟨i, z, hzlt, hzi, hzj⟩
          refine ⟨⟨z / b, (Nat.div_lt_iff_lt_mul hb).2 (by rw [Nat.mul_comm]; exact h ▸ hzlt)⟩, ?_⟩
          apply Subtype.ext
          apply Fin.ext
          have e := Nat.div_add_mod z b
          rw [hzj] at e
          show ((j : ℕ) + b * (z / b)) / A = (i : ℕ)
          rw [Nat.add_comm, e, hzi]
      have := Nat.card_eq_of_bijective _ hf
      rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
      exact this.symm

end BipartiteDD.GQST
