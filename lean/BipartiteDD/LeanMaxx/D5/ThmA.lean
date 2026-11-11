import BipartiteDD.LeanMaxx.D5.Level

/-! # D = 5 formalisation, part 4: Theorem A (level graphs) and the assembly theorems 3.5, 3.6

`research/theorems/D5_QUADRANGLE.md` §2 and §3.

* `Repaired D i j` is the condition (3.1) of Definition 3.3 for the arc `i → j`: for all `u, v` there is an
  unfreed `a ∈ A_i` with `d(u, a) + 1 + d(M a, v) ≤ 5`.
* `Hyp.repaired_of_empty` is the core of **Theorem A**: a transition without freed elements is repaired, for any
  typing and any bijection `M`. `Hyp.theoremA` states it for a whole level graph: `X(T, τ, M)` has diameter at
  most `5`, together with the explicit route form (`Hyp.route_of_empty`): the vertices of levels `i`, `j` of an arc
  `i → j` are joined by a walk of length at most `5` that is a walk in level `i`, one matching edge, a walk in
  level `j`.
* `Hyp.ediam_le_five` is **Theorem 3.6** (diameter `≤ 5` from (T') and (HG)); `Hyp.ediam_le_five_of_repaired`
  is **Theorem 3.5** (every transition repaired). The degree and order statement is in `Degree.lean`. -/

namespace BipartiteDD.LeanMaxx.D5

open SimpleGraph BipartiteDD

variable {P L : Type*} [Membership P L] {ι V U : Type*}

/-- The hypotheses used by the distance bounds. -/
structure Hyp (D : Data P L ι V U) : Prop where
  base : Base P L
  irrefl : ∀ i j, D.T i j → i ≠ j
  total : ∀ i j, i ≠ j → D.T i j ∨ D.T j i
  maps : ∀ i j, D.T i j → ∀ x, col x = D.τ i → col (D.M i j x) = !D.τ j
  onto : ∀ i j, D.T i j → ∀ y, col y = !D.τ j → col ((D.M i j).symm y) = D.τ i
  slotA : ∀ v i, col (D.slotV v i) = D.τ i
  slotB : ∀ u i, col (D.slotU u i) = !D.τ i

/-- Definition 3.3 through (3.1): the transition `i → j` is repaired. -/
def Data.Repaired (D : Data P L ι V U) (i j : ι) : Prop :=
  ∀ u v : P ⊕ L, ∃ a, col a = D.τ i ∧ a ∉ D.R i j ∧ ∃ m n : ℕ, m + 1 + n ≤ 5 ∧
    Reach (incGraph P L) u a m ∧ Reach (incGraph P L) (D.M i j a) v n

namespace Hyp

variable {D : Data P L ι V U} (H : Hyp D)
include H

/-- **Theorem A, route form.** A transition with no freed element is repaired. -/
theorem repaired_of_empty {i j : ι} (hT : D.T i j) (hR : D.R i j = ∅) : D.Repaired i j := by
  intro u v
  by_cases hu : col u = D.τ i
  · exact ⟨u, hu, by simp [hR], 0, 4, by norm_num, Reach.refl _ _, H.base.all4 _ _⟩
  · have hu' : col u = !D.τ i := by cases h1 : col u <;> cases h2 : D.τ i <;> simp_all
    by_cases hv : col v = !D.τ j
    · refine ⟨(D.M i j).symm v, H.onto i j hT v hv, by simp [hR], 3, 0, by norm_num, ?_, ?_⟩
      · apply H.base.odd3
        rw [hu', H.onto i j hT v hv]
        cases D.τ i <;> simp
      · simp [Reach.refl]
    · have hv' : col v = D.τ j := by cases h1 : col v <;> cases h2 : D.τ j <;> simp_all
      obtain ⟨b, -, -, hb, -⟩ := H.base.two v
      have hbcol : col b = !D.τ j := by rw [col_adj_not hb.symm, hv']
      refine ⟨(D.M i j).symm b, H.onto i j hT b hbcol, by simp [hR], 3, 1, by norm_num, ?_, ?_⟩
      · apply H.base.odd3
        rw [hu', H.onto i j hT b hbcol]
        cases D.τ i <;> simp
      · simpa using Reach.adj hb.symm

/-- A repaired transition joins the two levels within `5` in `X`. -/
theorem reach_of_repaired {i j : ι} (hT : D.T i j) (hr : D.Repaired i j) (x y : P ⊕ L) :
    Reach D.X (.inl (x, i)) (.inl (y, j)) 5 := by
  obtain ⟨a, haA, haR, m, n, hmn, h1, h2⟩ := hr x y
  have e1 := h1.map (D.lvl i)
  have e2 := Reach.adj (D.adj_shift (H.irrefl i j hT) hT haA haR)
  have e3 := h2.map (D.lvl j)
  exact ((e1.trans e2).trans e3).mono (by omega)

/-- Two vertices of one level are within `4`. -/
theorem level (x y : P ⊕ L) (i : ι) : Reach D.X (.inl (x, i)) (.inl (y, i)) 4 :=
  (H.base.all4 x y).map (D.lvl i)

/-- Lemma 3.4: a hub is within `5` of every level vertex. -/
theorem hub_level (h : V ⊕ U) (y : P ⊕ L) (i : ι) : Reach D.X (.inr h) (.inl (y, i)) 5 := by
  rcases h with v | u
  · exact ((Reach.adj (D.adj_slotV v i)).trans (H.level _ y i)).mono (by norm_num)
  · exact ((Reach.adj (D.adj_slotU u i)).trans (H.level _ y i)).mono (by norm_num)

/-- Lemma 3.4: a `𝓑`-hub is within `5` of every `𝓐`-hub. -/
theorem hub_hub [Nonempty ι] (v : V) (u : U) : Reach D.X (.inr (.inl v)) (.inr (.inr u)) 5 := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h1 := Reach.adj (D.adj_slotV v i)
  have h2 := (H.base.odd3 (D.slotV v i) (D.slotU u i) (by rw [H.slotA, H.slotB]; cases D.τ i <;> simp)).map
    (D.lvl i)
  have h3 := (Reach.adj (D.adj_slotU u i)).symm
  exact ((h1.trans h2).trans h3)

/-- **Theorem 3.6** (assembly, general form). If every arc satisfies (T') and same-colour hubs are within `4`,
then `X_R^+` has diameter at most `5`. -/
theorem ediam_le_five [Nonempty ι]
    (hT' : ∀ i j, D.T i j → ∀ x y : P ⊕ L, Reach D.X (.inl (x, i)) (.inl (y, j)) 5)
    (hgV : ∀ v v' : V, Reach D.X (.inr (.inl v)) (.inr (.inl v')) 4)
    (hgU : ∀ u u' : U, Reach D.X (.inr (.inr u)) (.inr (.inr u')) 4) : D.X.ediam ≤ 5 := by
  refine SimpleGraph.ediam_le_iff.2 fun a b => Reach.edist_le ?_
  rcases a with ⟨x, i⟩ | a <;> rcases b with ⟨y, i'⟩ | b
  · by_cases h : i = i'
    · subst h; exact (H.level x y i).mono (by norm_num)
    · rcases H.total i i' h with hT | hT
      · exact hT' i i' hT x y
      · exact (hT' i' i hT y x).symm
  · exact (H.hub_level b x i).symm
  · exact H.hub_level a y i'
  · rcases a with v | u <;> rcases b with v' | u'
    · exact (hgV v v').mono (by norm_num)
    · exact H.hub_hub v u'
    · exact (H.hub_hub v' u).symm
    · exact (hgU u u').mono (by norm_num)

/-- **Theorem 3.5** (assembly): every transition repaired, same-colour hubs within `4`. -/
theorem ediam_le_five_of_repaired [Nonempty ι]
    (hrep : ∀ i j, D.T i j → D.Repaired i j)
    (hgV : ∀ v v' : V, Reach D.X (.inr (.inl v)) (.inr (.inl v')) 4)
    (hgU : ∀ u u' : U, Reach D.X (.inr (.inr u)) (.inr (.inr u')) 4) : D.X.ediam ≤ 5 :=
  H.ediam_le_five (fun i j hT x y => H.reach_of_repaired hT (hrep i j hT) x y) hgV hgU

end Hyp

/-- **Theorem A.** For every tournament, typing and choice of bijections, the level graph (no freed element, no
hub) has diameter at most `5`. -/
theorem Hyp.theoremA {D : Data P L ι Empty Empty} (H : Hyp D) [Nonempty ι] (hR : ∀ i j, D.R i j = ∅) :
    D.X.ediam ≤ 5 :=
  H.ediam_le_five_of_repaired (fun i j hT => H.repaired_of_empty hT (hR i j))
    (fun v => v.elim) (fun u => u.elim)

end BipartiteDD.LeanMaxx.D5
