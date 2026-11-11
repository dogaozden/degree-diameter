import BipartiteDD.Haar.CycLift.Lift

/-! Fewer searches, using an automorphism that moves the base.

`Lift.lean` runs one search per base vertex. When the lift has an automorphism of the form
`(w, y) ↦ (π w, μ y)`, with `π` a permutation of the base and `μ` a unit mod `m`, the eccentricity of `(w, y)` is
that of `(π w, μ y)`, so one search per `π`-orbit of base vertices is enough.

The automorphism is checked on the base data alone (`autOK`): every arc `(u, β)` out of `w` has the arc
`(π u, μ β % m)` out of `π w`. Its inverse is given as `π'` and `μ'` (`invOK`). The orbits are covered by listing
`u₀, π u₀, π (π u₀), …` from each source (`orbL`, `orbOK`).

This is the shape of a Haar graph of a metacyclic group `Z_m ⋊_r Z_k` written as a `Z_m`-lift over its `2k`
cosets: right multiplication by `(0, 1)` shifts the cosets and multiplies the fibre coordinate by `r⁻¹`. -/

namespace BipartiteDD.CycLift

open BipartiteDD

/-- The lift map `(w, y) ↦ (π w, μ y % m)`. -/
def autMap (n m : ℕ) (π : ℕ → ℕ) (μ : ℕ) (v : Fin n) : Fin n :=
  ⟨(π (v.val / m) * m + μ * (v.val % m) % m) % n,
    Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) v.isLt)⟩

/-- `π` maps the base into itself, and every arc `(u, β)` out of `w` gives the arc `(π u, μ β % m)` out of `π w`. -/
def autOK (m b : ℕ) (π : ℕ → ℕ) (μ : ℕ) (outA : List (List (ℕ × ℕ))) : Bool :=
  (List.range b).all fun w => decide (π w < b) &&
    (outA.getD w []).all fun p => (outA.getD (π w) []).contains (π p.1, μ * p.2 % m)

/-- `π'` is a two-sided inverse of `π` on the base, and `μ' μ ≡ 1 (mod m)`. -/
def invOK (m b : ℕ) (π π' : ℕ → ℕ) (μ μ' : ℕ) : Bool :=
  (List.range b).all (fun w => decide (π' w < b) && decide (π (π' w) = w) && decide (π' (π w) = w)) &&
    decide (μ * μ' % m = 1 % m)

/-- `u₀, π u₀, …, π^(K-1) u₀`. -/
def orbL (π : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | K + 1, u => u :: orbL π K (π u)

/-- Every base vertex is in the `π`-orbit list of one of the sources. -/
def orbOK (b K : ℕ) (π : ℕ → ℕ) (srcs : List ℕ) : Bool :=
  (List.range b).all fun w => srcs.any fun u₀ => (orbL π K u₀).contains w

/-- The search from each source is full at radius `D`. -/
def eccSrcOK (m b D : ℕ) (outA : List (List (ℕ × ℕ))) (srcs : List ℕ) : Bool :=
  srcs.all fun u₀ => decide (u₀ < b) &&
    (levM m b outA u₀ D).all fun x => (x &&& (2 ^ m - 1)) == 2 ^ m - 1

theorem mem_orbL {π : ℕ → ℕ} : ∀ {K u w : ℕ}, w ∈ orbL π K u → ∃ i, π^[i] u = w
  | 0, _, _, h => by simp [orbL] at h
  | K + 1, u, w, h => by
    simp only [orbL, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, rfl⟩
    · obtain ⟨i, hi⟩ := mem_orbL h
      exact ⟨i + 1, by rw [Function.iterate_succ_apply]; exact hi⟩

theorem mul_add_mod' (a x y m : ℕ) : (a * x % m + a * y % m) % m = a * ((x + y) % m) % m := by
  rw [← Nat.add_mod, ← Nat.mul_add, Nat.mul_mod, Nat.mul_mod a ((x + y) % m), Nat.mod_mod]

theorem mul_inv_mod' (a a' y m : ℕ) (h : a * a' % m = 1 % m) : a * (a' * y % m) % m = y % m := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, Nat.mul_mod, h, ← Nat.mul_mod,
    Nat.one_mul]

section Aut

variable {n m b : ℕ} {outA : List (List (ℕ × ℕ))} {π π' : ℕ → ℕ} {μ μ' : ℕ}

theorem autMap_val (hn : n = b * m) (hm : 0 < m) (hπ : ∀ w < b, π w < b) (v : Fin n) :
    (autMap n m π μ v).val = π (v.val / m) * m + μ * (v.val % m) % m := by
  apply Nat.mod_eq_of_lt
  exact lt_of_lt_of_eq (lt_mul_of_lt (hπ _ (div_lt_of_fin hn v)) (Nat.mod_lt _ hm)) hn.symm

theorem autMap_div_mod (hn : n = b * m) (hm : 0 < m) (hπ : ∀ w < b, π w < b) (v : Fin n) :
    (autMap n m π μ v).val / m = π (v.val / m) ∧
      (autMap n m π μ v).val % m = μ * (v.val % m) % m := by
  rw [autMap_val hn hm hπ]
  exact div_mod_of_lt (Nat.mod_lt _ hm)

theorem pi_lt_of_autOK (h : autOK m b π μ outA = true) {w : ℕ} (hw : w < b) : π w < b := by
  have := List.all_eq_true.mp h w (List.mem_range.mpr hw)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1

/-- The lift map sends neighbours to neighbours. -/
theorem autMap_mem_nbrs (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true)
    (hφ : autOK m b π μ outA = true) {v w : Fin n} (h : w ∈ nbrs n m outA v) :
    autMap n m π μ w ∈ nbrs n m outA (autMap n m π μ v) := by
  have hπ : ∀ w < b, π w < b := fun w hw => pi_lt_of_autOK hφ hw
  obtain ⟨p, hp, hwv⟩ := val_of_mem_nbrs hn hm hA h
  have hv := div_lt_of_fin hn v
  have hwd : w.val / m = p.1 ∧ w.val % m = (v.val % m + p.2) % m := by
    rw [hwv]; exact div_mod_of_lt (Nat.mod_lt _ hm)
  have hφv := autMap_div_mod (μ := μ) hn hm hπ v
  have hφw := autMap_div_mod (μ := μ) hn hm hπ w
  have h0 : ((outA.getD (v.val / m) []).all fun p =>
      (outA.getD (π (v.val / m)) []).contains (π p.1, μ * p.2 % m)) = true := by
    have := List.all_eq_true.mp hφ (v.val / m) (List.mem_range.mpr hv)
    simp only [Bool.and_eq_true] at this
    exact this.2
  have harc : (π p.1, μ * p.2 % m) ∈ outA.getD ((autMap n m π μ v).val / m) [] := by
    have := List.all_eq_true.mp h0 _ hp
    rw [hφv.1]
    simpa using this
  obtain ⟨x, hxmem, hx1, hx2⟩ := mem_nbrs_of_arc hn hm hA (autMap n m π μ v) harc
  have : x = autMap n m π μ w := by
    apply fin_eq_of_div_mod
    · rw [hx1, hφw.1, hwd.1]
    · rw [hx2, hφw.2, hwd.2, hφv.2]
      exact mul_add_mod' μ _ _ m
  rw [← this]
  exact hxmem

/-- The lift map does not increase distances. -/
theorem edist_autMap_le (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true)
    (hφ : autOK m b π μ outA = true) (v w : Fin n) :
    (liftGraph n m outA).edist (autMap n m π μ v) (autMap n m π μ w) ≤
      (liftGraph n m outA).edist v w := by
  have hstep : ∀ x y : Fin n, (liftGraph n m outA).Adj x y →
      (liftGraph n m outA).edist (autMap n m π μ x) (autMap n m π μ y) ≤ 1 := by
    intro x y hxy
    rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
    by_cases he : autMap n m π μ x = autMap n m π μ y
    · exact Or.inr he
    · refine Or.inl ?_
      simp only [liftGraph, graphOf, SimpleGraph.fromRel_adj] at hxy ⊢
      refine ⟨he, ?_⟩
      rcases hxy.2 with h | h
      · exact Or.inl (autMap_mem_nbrs hn hm hA hφ h)
      · exact Or.inr (autMap_mem_nbrs hn hm hA hφ h)
  have hwalk : ∀ (x y : Fin n) (q : (liftGraph n m outA).Walk x y),
      (liftGraph n m outA).edist (autMap n m π μ x) (autMap n m π μ y) ≤ q.length := by
    intro x y q
    induction q with
    | nil => simp
    | cons hadj q ih =>
      rw [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one, add_comm]
      exact SimpleGraph.edist_triangle.trans (add_le_add (hstep _ _ hadj) ih)
  by_cases htop : (liftGraph n m outA).edist v w = ⊤
  · rw [htop]; exact le_top
  · obtain ⟨q, hq⟩ := SimpleGraph.exists_walk_of_edist_ne_top htop
    rw [← hq]
    exact hwalk v w q

/-- The lift map is onto. -/
theorem autMap_surj (hn : n = b * m) (hm : 0 < m) (hφ : autOK m b π μ outA = true)
    (hinv : invOK m b π π' μ μ' = true) (y : Fin n) :
    ∃ x : Fin n, x.val / m = π' (y.val / m) ∧ autMap n m π μ x = y := by
  have hπ : ∀ w < b, π w < b := fun w hw => pi_lt_of_autOK hφ hw
  simp only [invOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hinv
  obtain ⟨hpi, hmu⟩ := hinv
  have hy := div_lt_of_fin hn y
  obtain ⟨⟨h1, h2⟩, -⟩ := hpi _ hy
  have hlt : π' (y.val / m) * m + μ' * (y.val % m) % m < n :=
    lt_of_lt_of_eq (lt_mul_of_lt h1 (Nat.mod_lt _ hm)) hn.symm
  refine ⟨⟨_, hlt⟩, (div_mod_of_lt (Nat.mod_lt _ hm)).1, ?_⟩
  have hx := autMap_div_mod (μ := μ) hn hm hπ ⟨_, hlt⟩
  rw [(div_mod_of_lt (Nat.mod_lt _ hm)).1, (div_mod_of_lt (Nat.mod_lt _ hm)).2] at hx
  apply fin_eq_of_div_mod
  · rw [hx.1, h2]
  · rw [hx.2, mul_inv_mod' μ μ' _ m hmu, Nat.mod_mod]

end Aut

section Main

variable {n m b : ℕ} {outA : List (List (ℕ × ℕ))} {π π' : ℕ → ℕ} {μ μ' : ℕ}

/-- `v` reaches every vertex within `D` steps. -/
def Good (n m D : ℕ) (outA : List (List (ℕ × ℕ))) (v : Fin n) : Prop :=
  ∀ w, (liftGraph n m outA).edist v w ≤ D

/-- Every vertex over the base vertex `u` is good. -/
def GoodBase (n m D : ℕ) (outA : List (List (ℕ × ℕ))) (u : ℕ) : Prop :=
  ∀ v : Fin n, v.val / m = u → Good n m D outA v

theorem goodBase_pi (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true)
    (hφ : autOK m b π μ outA = true) (hinv : invOK m b π π' μ μ' = true) {D u : ℕ} (hu : u < b)
    (h : GoodBase n m D outA u) : GoodBase n m D outA (π u) := by
  intro v hv w
  obtain ⟨x, hx1, hx2⟩ := autMap_surj hn hm hφ hinv (μ' := μ') v
  obtain ⟨z, -, hz2⟩ := autMap_surj hn hm hφ hinv (μ' := μ') w
  have hinv' := hinv
  simp only [invOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hinv'
  have hxu : x.val / m = u := by rw [hx1, hv, (hinv'.1 u hu).2]
  rw [← hx2, ← hz2]
  exact (edist_autMap_le hn hm hA hφ x z).trans (h x hxu z)

theorem goodBase_iter (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true)
    (hφ : autOK m b π μ outA = true) (hinv : invOK m b π π' μ μ' = true) {D u : ℕ} (hu : u < b)
    (h : GoodBase n m D outA u) : ∀ i, GoodBase n m D outA (π^[i] u) ∧ π^[i] u < b := by
  intro i
  induction i with
  | zero => exact ⟨h, hu⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨goodBase_pi hn hm hA hφ hinv ih.2 ih.1, pi_lt_of_autOK hφ ih.2⟩

/-- A full search from `u₀` makes `u₀` good. -/
theorem goodBase_of_search (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true) {D u₀ : ℕ}
    (hfull : ((levM m b outA u₀ D).all fun x => (x &&& (2 ^ m - 1)) == 2 ^ m - 1) = true) :
    GoodBase n m D outA u₀ := by
  intro v hv w
  apply bfs_sound hn hm hA v D w
  have hw := div_lt_of_fin hn w
  have hlen := length_levM m b outA (v.val / m) D
  have hmem : (levM m b outA (v.val / m) D).getD (w.val / m) 0 ∈ levM m b outA (v.val / m) D := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hw),
      Option.getD_some]
    exact List.getElem_mem _
  rw [hv] at hmem ⊢
  have hx := List.all_eq_true.mp hfull _ hmem
  simp only [beq_iff_eq] at hx
  have hoff : off m (v.val % m) (w.val % m) < m := Nat.mod_lt _ hm
  have := congrArg (fun z => Nat.testBit z (off m (v.val % m) (w.val % m))) hx
  simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_one, hoff, decide_true, Bool.and_true] at this
  exact this

/-- Searches from the sources, with the automorphism and the orbit cover, bound every distance by `D`. -/
theorem edist_le_of_srcs (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true)
    (hφ : autOK m b π μ outA = true) (hinv : invOK m b π π' μ μ' = true) {D K : ℕ} {srcs : List ℕ}
    (horb : orbOK b K π srcs = true) (hE : eccSrcOK m b D outA srcs = true) (v w : Fin n) :
    (liftGraph n m outA).edist v w ≤ D := by
  have hv := div_lt_of_fin hn v
  have h1 := List.all_eq_true.mp horb (v.val / m) (List.mem_range.mpr hv)
  simp only [List.any_eq_true, List.contains_iff_mem] at h1
  obtain ⟨u₀, hu₀, hmem⟩ := h1
  obtain ⟨i, hi⟩ := mem_orbL hmem
  have h2 := List.all_eq_true.mp hE u₀ hu₀
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  have hg := (goodBase_iter hn hm hA hφ hinv h2.1 (goodBase_of_search hn hm hA h2.2) i).1
  rw [hi] at hg
  exact hg v rfl w

/-- The main theorem with sources: the base checks, the automorphism, the orbit cover and the searches from the
sources give a bipartite lift of degree at most `d` and diameter at most `D`. -/
theorem isBipartiteDegDiam_of_srcs {d D K : ℕ} (side : List Bool) (srcs : List ℕ)
    (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true) (hS : symOK m b outA = true)
    (hd : degOK d b outA = true) (hc : colOK b side outA = true)
    (hφ : autOK m b π μ outA = true) (hinv : invOK m b π π' μ μ' = true)
    (horb : orbOK b K π srcs = true) (hE : eccSrcOK m b D outA srcs = true) :
    IsBipartiteDegDiam (liftGraph n m outA) d D :=
  isBipartiteDegDiam_of_edist side hn hm hA hS hd hc (edist_le_of_srcs hn hm hA hφ hinv horb hE)

end Main

end BipartiteDD.CycLift
