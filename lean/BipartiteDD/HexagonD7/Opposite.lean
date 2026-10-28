import BipartiteDD.HexagonD7.Balls

/-! Diameter 7 from a generalized hexagon, part 7: **Lemma 2** (THEOREM.md §4) and pairwise opposite sets.

`exists_local_duality`: if the closed 2-balls of the points of `R` are pairwise disjoint, those of the lines of
`S` too, and `|R| = |S|`, then some bijection `σ : P ≃ L` maps the points collinear with each `r ∈ R` onto the lines
concurrent with `σ r` (condition (R2)), with `σ r = τ r` for a given `τ : R ≃ S`.
`exists_disjoint_ballsP` / `exists_disjoint_ballsL`: there are `k` such points (lines) as long as
`k (1 + (q+1) q)² < |P|` (greedy). -/

namespace BipartiteDD.HexagonD7

open Finset
open scoped Classical

variable {P L : Type*} [Fintype P] [Fintype L] {inc : P → L → Prop} {q : ℕ}
  (hdig : ∀ {p r : P} {M₁ M₂ : L}, p ≠ r → inc p M₁ → inc r M₁ → inc p M₂ → inc r M₂ → M₁ = M₂)
  (hP : ∀ p, (univ.filter (inc p)).card = q + 1) (hL : ∀ l, (univ.filter (fun p => inc p l)).card = q + 1)

section Greedy

include hdig hP hL

theorem card_bad_le (r : P) : ((ballP inc r).biUnion (ballP inc)).card ≤ (1 + (q + 1) * q) ^ 2 := by
  refine (card_biUnion_le).trans ?_
  rw [sum_congr rfl (fun y _ => card_ballP hdig hP hL y), sum_const, card_ballP hdig hP hL r, smul_eq_mul]
  ring_nf; exact le_rfl

theorem card_badL_le (l : L) : ((ballL inc l).biUnion (ballL inc)).card ≤ (1 + (q + 1) * q) ^ 2 := by
  refine (card_biUnion_le).trans ?_
  rw [sum_congr rfl (fun y _ => card_ballL hdig hP hL y), sum_const, card_ballL hdig hP hL l, smul_eq_mul]
  ring_nf; exact le_rfl

/-- Greedy: `k` points with pairwise disjoint closed 2-balls (pairwise opposite points). -/
theorem exists_disjoint_ballsP : ∀ k : ℕ, k * (1 + (q + 1) * q) ^ 2 < Fintype.card P →
    ∃ R : Finset P, R.card = k ∧ ∀ r ∈ R, ∀ s ∈ R, r ≠ s → Disjoint (ballP inc r) (ballP inc s) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨∅, by simp, by simp⟩
  | succ k ih =>
    intro hk
    obtain ⟨R, hRc, hR⟩ := ih (lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_succ k)) hk)
    set Bad := R.biUnion (fun r => (ballP inc r).biUnion (ballP inc)) with hBad
    have hBc : Bad.card < Fintype.card P := by
      have h1 := card_biUnion_le (s := R) (t := fun r => (ballP inc r).biUnion (ballP inc))
      have h2 : ∑ r ∈ R, ((ballP inc r).biUnion (ballP inc)).card ≤ ∑ _r ∈ R, (1 + (q + 1) * q) ^ 2 :=
        sum_le_sum (fun r _ => card_bad_le hdig hP hL r)
      rw [sum_const, hRc, smul_eq_mul] at h2
      have h3 : k * (1 + (q + 1) * q) ^ 2 ≤ (k + 1) * (1 + (q + 1) * q) ^ 2 :=
        Nat.mul_le_mul_right _ (Nat.le_succ k)
      rw [hBad]; omega
    obtain ⟨z, hz⟩ : ∃ z, z ∉ Bad := by
      by_contra h; push_neg at h
      have : Bad = univ := eq_univ_of_forall h
      rw [this, card_univ] at hBc; exact lt_irrefl _ hBc
    have hzR : z ∉ R := by
      intro hzr; apply hz; rw [hBad, mem_biUnion]
      exact ⟨z, hzr, mem_biUnion.2 ⟨z, self_mem_ballP z, self_mem_ballP z⟩⟩
    have hdz : ∀ s ∈ R, Disjoint (ballP inc z) (ballP inc s) := by
      intro s hs
      rw [Finset.disjoint_left]
      intro y hy hy'
      apply hz; rw [hBad, mem_biUnion]
      exact ⟨s, hs, mem_biUnion.2 ⟨y, hy', mem_ballP_comm.1 hy⟩⟩
    refine ⟨insert z R, by rw [card_insert_of_notMem hzR, hRc], ?_⟩
    intro r hr s hs hrs
    rw [mem_insert] at hr hs
    rcases hr with rfl | hr <;> rcases hs with rfl | hs
    · exact absurd rfl hrs
    · exact hdz s hs
    · exact (hdz r hr).symm
    · exact hR r hr s hs hrs

/-- Greedy: `k` lines with pairwise disjoint closed 2-balls (pairwise opposite lines). -/
theorem exists_disjoint_ballsL : ∀ k : ℕ, k * (1 + (q + 1) * q) ^ 2 < Fintype.card L →
    ∃ S : Finset L, S.card = k ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Disjoint (ballL inc a) (ballL inc b) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨∅, by simp, by simp⟩
  | succ k ih =>
    intro hk
    obtain ⟨S, hSc, hS⟩ := ih (lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_succ k)) hk)
    set Bad := S.biUnion (fun a => (ballL inc a).biUnion (ballL inc)) with hBad
    have hBc : Bad.card < Fintype.card L := by
      have h1 := card_biUnion_le (s := S) (t := fun a => (ballL inc a).biUnion (ballL inc))
      have h2 : ∑ a ∈ S, ((ballL inc a).biUnion (ballL inc)).card ≤ ∑ _a ∈ S, (1 + (q + 1) * q) ^ 2 :=
        sum_le_sum (fun a _ => card_badL_le hdig hP hL a)
      rw [sum_const, hSc, smul_eq_mul] at h2
      have h3 : k * (1 + (q + 1) * q) ^ 2 ≤ (k + 1) * (1 + (q + 1) * q) ^ 2 :=
        Nat.mul_le_mul_right _ (Nat.le_succ k)
      rw [hBad]; omega
    obtain ⟨z, hz⟩ : ∃ z, z ∉ Bad := by
      by_contra h; push_neg at h
      have : Bad = univ := eq_univ_of_forall h
      rw [this, card_univ] at hBc; exact lt_irrefl _ hBc
    have hzS : z ∉ S := by
      intro hzs; apply hz; rw [hBad, mem_biUnion]
      exact ⟨z, hzs, mem_biUnion.2 ⟨z, self_mem_ballL z, self_mem_ballL z⟩⟩
    have hdz : ∀ b ∈ S, Disjoint (ballL inc z) (ballL inc b) := by
      intro b hb
      rw [Finset.disjoint_left]
      intro y hy hy'
      apply hz; rw [hBad, mem_biUnion]
      exact ⟨b, hb, mem_biUnion.2 ⟨y, hy', mem_ballL_comm.1 hy⟩⟩
    refine ⟨insert z S, by rw [card_insert_of_notMem hzS, hSc], ?_⟩
    intro a ha b hb hab
    rw [mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact hdz b hb
    · exact (hdz a ha).symm
    · exact hS a ha b hb hab

end Greedy

end BipartiteDD.HexagonD7
