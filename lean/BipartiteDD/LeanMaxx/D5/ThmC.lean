import BipartiteDD.LeanMaxx.D5.ThmE

/-! # D = 5 formalisation, part 11: Theorem C (local dualities)

`research/theorems/D5_QUADRANGLE.md` §6. If the freed set `R` of the arc `i → j` satisfies

* (H1) no two elements of `R` are at distance two (non-collinear / non-concurrent), and
* (H3) `M` maps `Γ₂(x)` onto `Γ₂(M x)` for every `x ∈ R` (here: for `a ∈ A_i`, `Co x a ↔ Co (M x) (M a)`),

then the transition is repaired. (At `D = 7` the analogous theorem also needs (H2); at `D = 5` it is not needed.) -/

namespace BipartiteDD.LeanMaxx.D5

open SimpleGraph BipartiteDD

variable {P L : Type*} [Membership P L] {ι V U : Type*}

namespace Hyp

variable {D : Data P L ι V U} (H : Hyp D)
include H

/-- **Theorem C.** (H1) and (H3) imply (E2) and (E3), hence the transition is repaired. -/
theorem repaired_of_local_dual {i j : ι} (hT : D.T i j) (hRA : ∀ x ∈ D.R i j, col x = D.τ i)
    (h1 : ∀ x ∈ D.R i j, ∀ y ∈ D.R i j, x ≠ y → ¬ Co x y)
    (h3 : ∀ x ∈ D.R i j, ∀ a, col a = D.τ i → (Co x a ↔ Co (D.M i j x) (D.M i j a))) :
    D.Repaired i j := by
  by_cases hne : (D.R i j).Nonempty
  · refine H.repaired_of_E hT hRA hne ?_ ?_
    · intro x hx y hy
      have hxc : col (D.M i j x) = !D.τ j := H.maps i j hT x (hRA x hx)
      obtain ⟨z, hz, hzy⟩ := H.base.cover (D.M i j x) y (by rw [hxc, hy]; cases D.τ j <;> simp)
      have hzc : col z = !D.τ j := by rw [← hz.col_eq, hxc]
      set a := (D.M i j).symm z with ha
      have haA : col a = D.τ i := H.onto i j hT z hzc
      have hMa : D.M i j a = z := by simp [ha]
      have hco : Co x a := (h3 x hx a haA).2 (by rw [hMa]; exact hz)
      exact ⟨a, hco, fun haR => h1 x hx a haR hco.1 hco, by rw [hMa]; exact hzy⟩
    · intro x hx b hb
      obtain ⟨z, hz, hzb⟩ := H.base.cover x b (by rw [hRA x hx, hb]; cases D.τ i <;> simp)
      have hzc : col z = D.τ i := by rw [← hz.col_eq, hRA x hx]
      exact ⟨z, fun hzR => h1 x hx z hzR hz.1 hz, hzb.symm, (h3 x hx z hzc).1 hz⟩
  · exact H.repaired_of_empty hT (Set.not_nonempty_iff_eq_empty.1 hne)

end Hyp

end BipartiteDD.LeanMaxx.D5
