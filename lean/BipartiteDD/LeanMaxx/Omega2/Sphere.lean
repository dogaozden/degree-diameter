import BipartiteDD.Doubling.Hat
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Sphere sizes in a generalized hexagon of order `(q, q)`

`B` is the incidence graph of a generalized hexagon (`GenPolygonGraph B 6`) on a finite type, with
every vertex of degree `q + 1`, and `κ : β → ZMod 2` a proper 2-colouring.
`sph B u d` is the set of vertices at distance exactly `d` from `u`.

* `card_sph_zero`, `card_sph_of_le_five`: `|sph u 0| = 1` and `|sph u d| = (q+1) q^(d-1)` for `1 ≤ d ≤ 5`.
* `q_pow_five_le_card_sph_six`: `q^5 ≤ |sph u 6|` (equality holds, only the inequality is needed).
-/



set_option linter.unusedSectionVars false

namespace BipartiteDD.LeanMaxx.Omega2

open SimpleGraph Finset

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The sphere of radius `d` around `u`. -/
noncomputable def sph (B : SimpleGraph β) (u : β) (d : ℕ) : Finset β := univ.filter fun v => B.dist u v = d

theorem mem_sph {B : SimpleGraph β} {u v : β} {d : ℕ} : v ∈ sph B u d ↔ B.dist u v = d := by
  simp [sph]

section

variable {B : SimpleGraph β} [DecidableRel B.Adj]

omit [Fintype β] [DecidableEq β] [DecidableRel B.Adj] in
theorem reachable_of_ediam {n : ℕ} (h : B.ediam = (n : ℕ∞)) (u v : β) : B.Reachable u v := by
  have h1 : B.edist u v ≤ B.ediam := edist_le_ediam
  rw [h] at h1
  exact edist_ne_top_iff_reachable.mp (ne_top_of_le_ne_top (by simp) h1)

omit [Fintype β] [DecidableEq β] [DecidableRel B.Adj] in
theorem dist_le_of_ediam {n : ℕ} (h : B.ediam = (n : ℕ∞)) (u v : β) : B.dist u v ≤ n := by
  have h1 : B.edist u v ≤ B.ediam := edist_le_ediam
  rw [h] at h1
  have hr := reachable_of_ediam h u v
  rw [← hr.coe_dist_eq_edist] at h1
  exact_mod_cast h1

omit [Fintype β] [DecidableEq β] [DecidableRel B.Adj] in
/-- Colour along a walk. -/
theorem col_walk {κ : β → ZMod 2} (hκ : ∀ u v, B.Adj u v → κ u ≠ κ v) {a b : β} (p : B.Walk a b) :
    κ b = κ a + (p.length : ZMod 2) := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
    have hne := hκ x y h
    have : κ y = κ x + 1 := by
      revert hne; generalize κ x = s; generalize κ y = t; revert s t; decide
    rw [ih, this, Walk.length_cons]; push_cast; ring

theorem col_dist {κ : β → ZMod 2} (hκ : ∀ u v, B.Adj u v → κ u ≠ κ v) {a b : β}
    (hr : B.Reachable a b) : κ b = κ a + (B.dist a b : ZMod 2) := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  rw [← hp]; exact col_walk hκ p

theorem zmod2_eq_add_one {s t : ZMod 2} (h : s ≠ t) : t = s + 1 := by
  revert h; revert s t; decide

/-- Girth: a vertex at distance `d + 1 ≤ 5` has at most one neighbour at distance `d`. -/
theorem pred_unique {u : β} (hg : B.egirth = ((2 * 6 : ℕ) : ℕ∞)) (hr : ∀ u v : β, B.Reachable u v)
    {v y₁ y₂ : β} {d : ℕ} (hd : d ≤ 4) (hv : B.dist u v = d + 1) (h1 : B.Adj v y₁) (h2 : B.Adj v y₂)
    (hy1 : B.dist u y₁ = d) (hy2 : B.dist u y₂ = d) : y₁ = y₂ := by
  by_contra hne
  obtain ⟨g1, hg1⟩ := (hr u y₁).exists_walk_length_eq_dist
  obtain ⟨g2, hg2⟩ := (hr u y₂).exists_walk_length_eq_dist
  have key : ∀ {z : β} (g : B.Walk u z), g.length = d → v ∈ g.support → False := by
    intro z g hgl hmem
    have hl := congrArg Walk.length (Walk.take_spec g hmem)
    rw [Walk.length_append] at hl
    have := dist_le (g.takeUntil v hmem)
    omega
  have hvW : v ∉ (g1.reverse.append g2).support := by
    intro hmem
    have hmem' : v ∈ g1.reverse.support ∨ v ∈ g2.support.tail := by
      simpa [Walk.support_append] using hmem
    rcases hmem' with h | h
    · exact key g1 (hg1.trans hy1) (by simpa using h)
    · exact key g2 (hg2.trans hy2) (List.mem_of_mem_tail h)
  have hlen : (g1.reverse.append g2).length = 2 * d := by
    simp only [Walk.length_append, Walk.length_reverse]; omega
  have hbp := Walk.bypass_isPath (g1.reverse.append g2)
  have hsub := Walk.support_bypass_subset_support (g1.reverse.append g2)
  have hle := Walk.length_bypass_le_length (g1.reverse.append g2)
  generalize (g1.reverse.append g2).bypass = P at hbp hsub hle
  rw [hlen] at hle
  have hvP : v ∉ P.support := fun h => hvW (hsub h)
  have hpath : (P.concat h2.symm).IsPath := Walk.IsPath.concat hbp hvP h2.symm
  have hcyc : (Walk.cons h1 (P.concat h2.symm)).IsCycle := by
    rw [Walk.cons_isCycle_iff]
    refine ⟨hpath, ?_⟩
    intro hmem
    rw [Walk.edges_concat, List.concat_eq_append, List.mem_append] at hmem
    rcases hmem with h | h
    · exact hvP (Walk.fst_mem_support_of_mem_edges P h)
    · simp only [List.mem_singleton, Sym2.eq_iff] at h
      rcases h with ⟨ha, hb⟩ | ⟨_, hb⟩
      · exact hne (hb.trans ha)
      · exact hne hb
  have h12 := hcyc.egirth_le_length
  rw [hg] at h12
  simp only [Walk.length_cons, Walk.length_concat] at h12
  have : (12 : ℕ) ≤ P.length + 1 + 1 := by exact_mod_cast h12
  omega


/-! ### Layers -/

variable {κ : β → ZMod 2} (hκ : ∀ u v, B.Adj u v → κ u ≠ κ v)

include hκ in
/-- A neighbour of a vertex at distance `d` is at distance `d + 1`, or `d - 1`. -/
theorem nbr_dist (hr : ∀ u v : β, B.Reachable u v) {u v y : β} (h : B.Adj v y) :
    B.dist u y = B.dist u v + 1 ∨ B.dist u y + 1 = B.dist u v := by
  have hcol := hκ v y h
  have c1 := col_dist hκ (hr u v)
  have c2 := col_dist hκ (hr u y)
  rcases h.diff_dist_adj (u := u) with h1 | h1 | h1
  · exfalso; apply hcol; rw [c1, c2, h1]
  · exact Or.inl h1
  · right
    have hpos : 0 < B.dist u v := by
      by_contra h0
      have h0' : B.dist u v = 0 := by omega
      have hy : B.dist u y = 0 := by omega
      have e1 := (hr u v).dist_eq_zero_iff.mp h0'
      have e2 := (hr u y).dist_eq_zero_iff.mp hy
      exact h.ne (e1.symm.trans e2)
    omega

/-- Every vertex at distance `e + 1` has a neighbour at distance `e`. -/
theorem exists_pred (hr : ∀ u v : β, B.Reachable u v) {u v : β} {e : ℕ} (hv : B.dist u v = e + 1) :
    ∃ y, B.Adj v y ∧ B.dist u y = e := by
  haveI : Nonempty β := ⟨u⟩
  have hc : B.Connected := ⟨hr⟩
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u v
  cases hq : p.reverse with
  | nil =>
    have h0 : p.length = 0 := by rw [← Walk.length_reverse, hq]; rfl
    omega
  | @cons _ y _ h p' =>
    refine ⟨y, h, ?_⟩
    have hl : p'.length = e := by
      have := congrArg Walk.length hq
      rw [Walk.length_reverse, Walk.length_cons] at this
      omega
    have h1 : B.dist y u ≤ e := hl ▸ dist_le p'
    rw [dist_comm] at h1
    have h2 : B.dist u v ≤ B.dist u y + B.dist y v := hc.dist_triangle
    have h3 : B.dist y v = 1 := dist_eq_one_iff_adj.mpr h.symm
    omega


section Hex

variable {q : ℕ} (hdeg : ∀ v, B.degree v = q + 1)
  (hg : B.egirth = ((2 * 6 : ℕ) : ℕ∞)) (hr : ∀ u v : β, B.Reachable u v) {u : β}

include hκ hg hr in
theorem below_card {e : ℕ} (he : e ≤ 4) {v : β} (hv : B.dist u v = e + 1) :
    ((B.neighborFinset v).filter fun y => B.dist u y = e).card = 1 := by
  rw [Finset.card_eq_one]
  obtain ⟨y, hy, hyd⟩ := exists_pred hr hv
  refine ⟨y, ?_⟩
  ext z
  simp only [Finset.mem_filter, mem_neighborFinset, Finset.mem_singleton]
  constructor
  · rintro ⟨hz, hzd⟩
    exact pred_unique hg hr he hv hz hy hzd hyd
  · rintro rfl; exact ⟨hy, hyd⟩

include hκ hdeg hg hr in
theorem above_card {e : ℕ} (he : e ≤ 4) {v : β} (hv : B.dist u v = e + 1) :
    ((B.neighborFinset v).filter fun y => B.dist u y = e + 2).card = q := by
  have h1 := below_card hκ hg hr he hv
  have h2 := Finset.card_filter_add_card_filter_not (s := B.neighborFinset v)
    (fun y => B.dist u y = e)
  rw [h1, card_neighborFinset_eq_degree, hdeg] at h2
  have : (B.neighborFinset v).filter (fun y => ¬ B.dist u y = e) =
      (B.neighborFinset v).filter fun y => B.dist u y = e + 2 := by
    apply Finset.filter_congr
    intro y hy
    rw [mem_neighborFinset] at hy
    have := nbr_dist hκ hr (u := u) hy
    omega
  rw [this] at h2
  omega

include hκ hg hr in
theorem cnt_below {e : ℕ} (he : e ≤ 3) {y : β} (hy : B.dist u y = e + 2) :
    ((sph B u (e + 1)).filter fun v => B.Adj v y).card = 1 := by
  have h := below_card hκ hg hr (u := u) (v := y) (by omega) hy
  have hset : (sph B u (e + 1)).filter (fun v => B.Adj v y) =
      (B.neighborFinset y).filter fun z => B.dist u z = e + 1 := by
    ext z
    simp only [Finset.mem_filter, mem_sph, mem_neighborFinset]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2.symm, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1.symm⟩
  rw [hset]; exact h

include hκ hdeg hg hr in
theorem card_sph_succ {e : ℕ} (he : e ≤ 3) :
    (sph B u (e + 2)).card = q * (sph B u (e + 1)).card := by
  have := Finset.card_mul_eq_card_mul (s := sph B u (e + 1)) (t := sph B u (e + 2)) (r := B.Adj)
    (m := q) (n := 1) ?_ ?_
  · rw [mul_one, mul_comm] at this; exact this.symm
  · intro v hv
    rw [mem_sph] at hv
    have h := above_card hκ hdeg hg hr (u := u) (e := e) (by omega) hv
    have hset : (sph B u (e + 2)).filter (fun z => B.Adj v z) =
        (B.neighborFinset v).filter fun z => B.dist u z = e + 2 := by
      ext z
      simp [mem_sph, mem_neighborFinset, and_comm]
    unfold Finset.bipartiteAbove
    rw [hset]; exact h
  · intro y hy
    rw [mem_sph] at hy
    exact cnt_below hκ hg hr he hy

include hr in
theorem card_sph_zero : (sph B u 0).card = 1 := by
  have : sph B u 0 = {u} := by
    ext z
    simp [mem_sph, (hr u z).dist_eq_zero_iff, eq_comm]
  rw [this]; rfl

include hdeg in
theorem card_sph_one : (sph B u 1).card = q + 1 := by
  have : sph B u 1 = B.neighborFinset u := by
    ext z; simp [mem_sph, mem_neighborFinset]
  rw [this, card_neighborFinset_eq_degree, hdeg]

include hκ hdeg hg hr in
theorem card_sph_five : (sph B u 5).card = (q + 1) * q ^ 4 := by
  have h1 := card_sph_one hdeg (u := u)
  have h2 := card_sph_succ hκ hdeg hg hr (u := u) (e := 0) (by omega)
  have h3 := card_sph_succ hκ hdeg hg hr (u := u) (e := 1) (by omega)
  have h4 := card_sph_succ hκ hdeg hg hr (u := u) (e := 2) (by omega)
  have h5 := card_sph_succ hκ hdeg hg hr (u := u) (e := 3) (by omega)
  simp only [Nat.reduceAdd, zero_add] at h2 h3 h4 h5
  rw [h5, h4, h3, h2, h1]; ring

include hκ hdeg hg hr in
theorem q_pow_five_le_card_sph_six (hq : 1 ≤ q) : q ^ 5 ≤ (sph B u 6).card := by
  have h5 := card_sph_five hκ hdeg hg hr (u := u)
  have key := Finset.card_mul_le_card_mul (s := sph B u 5) (t := sph B u 6) (r := B.Adj)
    (m := q) (n := q + 1) ?_ ?_
  · rw [h5] at key
    have : (q + 1) * q ^ 5 ≤ (q + 1) * (sph B u 6).card := by
      calc (q + 1) * q ^ 5 = (q + 1) * q ^ 4 * q := by ring
        _ ≤ (sph B u 6).card * (q + 1) := key
        _ = (q + 1) * (sph B u 6).card := by ring
    exact Nat.le_of_mul_le_mul_left this (by omega)
  · intro v hv
    rw [mem_sph] at hv
    have h := above_card hκ hdeg hg hr (u := u) (e := 4) (by omega) hv
    have hset : (sph B u 6).filter (fun z => B.Adj v z) =
        (B.neighborFinset v).filter fun z => B.dist u z = 4 + 2 := by
      ext z
      simp [mem_sph, mem_neighborFinset, and_comm]
    unfold Finset.bipartiteAbove
    rw [hset, h]
  · intro y _
    have hsub : (sph B u 5).filter (fun z => B.Adj z y) ⊆ B.neighborFinset y := by
      intro z hz
      rw [Finset.mem_filter] at hz
      rw [mem_neighborFinset]; exact hz.2.symm
    unfold Finset.bipartiteBelow
    calc _ ≤ (B.neighborFinset y).card := Finset.card_le_card hsub
      _ = q + 1 := by rw [card_neighborFinset_eq_degree, hdeg]

end Hex

end

end BipartiteDD.LeanMaxx.Omega2
