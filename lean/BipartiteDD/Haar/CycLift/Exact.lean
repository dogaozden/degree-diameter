import BipartiteDD.Haar.CycLift.Aut

/-! Exact degree and exact diameter for the lifts of `Lift.lean`.

`IsBipartiteDegDiam` bounds the degree and the diameter from above, which is what a record needs. Here the search is
shown to be complete as well as sound (`bfs_complete`: a walk of length `r` from `w` to `v` sets the bit of `w` in
the search from `v / m` at radius `r`). So a search that is not full at radius `D - 1` gives two vertices at distance
at least `D`, and with the upper bound the diameter is exactly `D` (`ediam_eq_of`). With no repeated arc at a base
vertex and exactly `d` arcs at each, every vertex has exactly `d` neighbours (`ncard_neighborSet_eq`). -/

namespace BipartiteDD.CycLift

open BipartiteDD

/-- Every base vertex has exactly `d` arcs, with no repeats. -/
def regOK (d b : ℕ) (outA : List (List (ℕ × ℕ))) : Bool :=
  (List.range b).all fun w => decide ((outA.getD w []).length = d) && decide (outA.getD w []).Nodup

/-- Some search from a source is not full at radius `D'`. -/
def eccFailOK (m b D' : ℕ) (outA : List (List (ℕ × ℕ))) (srcs : List ℕ) : Bool :=
  srcs.any fun u₀ => decide (u₀ < b) &&
    (levM m b outA u₀ D').any fun x => (x &&& (2 ^ m - 1)) != 2 ^ m - 1

section Complete

variable {n m b : ℕ} {outA : List (List (ℕ × ℕ))}

/-- The step keeps every bit. -/
theorem testBit_stepM_of {cur : List ℕ} {w z : ℕ} (hw : w < b) (h : (cur.getD w 0).testBit z = true) :
    ((stepM m b outA cur).getD w 0).testBit z = true := by
  simp only [stepM, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hw,
    Option.map_some, Option.getD_some]
  simp only [← List.getD_eq_getElem?_getD]
  rw [testBit_foldl_or']
  exact Or.inl h

/-- The search only grows with the radius. -/
theorem testBit_levM_mono {u₀ w z : ℕ} (hw : w < b) {r : ℕ}
    (h : ((levM m b outA u₀ r).getD w 0).testBit z = true) :
    ∀ s, r ≤ s → ((levM m b outA u₀ s).getD w 0).testBit z = true := by
  intro s hs
  induction s with
  | zero =>
    have : r = 0 := by omega
    subst this; exact h
  | succ s ih =>
    by_cases hrs : r = s + 1
    · subst hrs; exact h
    · exact testBit_stepM_of hw (ih (by omega))

/-- Completeness of the search: a walk of length `L` from `u` to `v` sets the bit of `u` at radius `L` of the search
from `v / m`. -/
theorem bfs_complete_walk (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true)
    (hS : symOK m b outA = true) :
    ∀ (u v : Fin n) (q : (liftGraph n m outA).Walk u v),
      ((levM m b outA (v.val / m) q.length).getD (u.val / m) 0).testBit
        (off m (v.val % m) (u.val % m)) = true := by
  intro u v q
  induction q with
  | nil =>
    rename_i x
    have hx := div_lt_of_fin hn x
    simp only [SimpleGraph.Walk.length_nil, levM, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hx, Option.map_some, Option.getD_some, ↓reduceIte, off_self]
    rfl
  | cons hadj q ih =>
    rename_i x y z
    have hx := div_lt_of_fin hn x
    rw [SimpleGraph.Walk.length_cons]
    have hlev : levM m b outA (z.val / m) (q.length + 1) =
        stepM m b outA (levM m b outA (z.val / m) q.length) := rfl
    rw [hlev]
    simp only [stepM, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hx,
      Option.map_some, Option.getD_some]
    simp only [← List.getD_eq_getElem?_getD]
    rw [testBit_foldl_or']
    right
    -- `y` is a neighbour of `x` in the list of `x`
    have hy : y ∈ nbrs n m outA x := by
      simp only [liftGraph, graphOf, SimpleGraph.fromRel_adj] at hadj
      rcases hadj.2 with h | h
      · exact h
      · exact mem_nbrs_symm hn hm hA hS h
    obtain ⟨p, hp, hyv⟩ := val_of_mem_nbrs hn hm hA hy
    obtain ⟨hp1, hp2⟩ := of_arcsOK hA hx hp
    have hyd : y.val / m = p.1 ∧ y.val % m = (x.val % m + p.2) % m := by
      rw [hyv]; exact div_mod_of_lt (Nat.mod_lt _ hm)
    refine ⟨p, hp, ?_⟩
    have hoff : off m (z.val % m) (x.val % m) < m := Nat.mod_lt _ hm
    rw [testBit_rotR hp2 hoff, ← off_step (Nat.mod_lt _ hm), ← hyd.2, ← hyd.1]
    exact ih

/-- Completeness at a distance: `edist v w ≤ r` sets the bit of `w` at radius `r` of the search from `v / m`. -/
theorem bfs_complete (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true)
    (hS : symOK m b outA = true) (v w : Fin n) (r : ℕ) (h : (liftGraph n m outA).edist v w ≤ r) :
    ((levM m b outA (v.val / m) r).getD (w.val / m) 0).testBit (off m (v.val % m) (w.val % m)) = true := by
  have hne : (liftGraph n m outA).edist w v ≠ ⊤ := by
    rw [SimpleGraph.edist_comm]
    exact ne_top_of_le_ne_top (by simp) h
  obtain ⟨q, hq⟩ := SimpleGraph.exists_walk_of_edist_ne_top hne
  have hlen : q.length ≤ r := by
    have : ((q.length : ℕ) : ℕ∞) ≤ r := by rw [hq, SimpleGraph.edist_comm]; exact h
    exact_mod_cast this
  exact testBit_levM_mono (div_lt_of_fin hn w) (bfs_complete_walk hn hm hA hS w v q) r hlen

/-- A search from `u₀` that is not full at radius `D'` gives two vertices at distance more than `D'`. -/
theorem exists_far (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true)
    (hS : symOK m b outA = true) {D' : ℕ} {srcs : List ℕ} (hF : eccFailOK m b D' outA srcs = true) :
    ∃ v w : Fin n, ¬ (liftGraph n m outA).edist v w ≤ D' := by
  simp only [eccFailOK, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
    ne_eq] at hF
  obtain ⟨u₀, -, hu₀, x, hx, hxne⟩ := hF
  have hlen := length_levM m b outA u₀ D'
  obtain ⟨w', hw', hxw⟩ := List.getElem_of_mem hx
  have hwb : w' < b := by rw [← hlen]; exact hw'
  -- a bit below `m` that is not set
  have : ∃ z < m, x.testBit z = false := by
    by_contra hcon
    push Not at hcon
    apply hxne
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    by_cases hi : i < m
    · have := hcon i hi
      simp only [ne_eq, Bool.not_eq_false] at this
      simp [this, hi]
    · simp [hi]
  obtain ⟨z, hz, hxz⟩ := this
  have hv : u₀ * m + 0 < n := lt_of_lt_of_eq (lt_mul_of_lt hu₀ hm) hn.symm
  have hw : w' * m + z < n := lt_of_lt_of_eq (lt_mul_of_lt hwb hz) hn.symm
  refine ⟨⟨_, hv⟩, ⟨_, hw⟩, fun hle => ?_⟩
  have h := bfs_complete hn hm hA hS _ _ D' hle
  have e1 := div_mod_of_lt (u := u₀) hm
  have e2 := div_mod_of_lt (u := w') hz
  simp only at h
  rw [e1.1, e1.2, e2.1, e2.2] at h
  have hoff : off m 0 z = z := by
    unfold off; rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hz]
  rw [hoff, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw', Option.getD_some, hxw] at h
  rw [h] at hxz
  exact Bool.noConfusion hxz

/-- The diameter is exactly `D` (`D ≥ 1`): at most `D` by the upper bound, and the failed search at `D - 1` gives
a pair at distance at least `D`. -/
theorem ediam_eq_of (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true)
    (hS : symOK m b outA = true) {D : ℕ} (hD : 0 < D) {srcs : List ℕ}
    (hle : ∀ v w : Fin n, (liftGraph n m outA).edist v w ≤ D)
    (hF : eccFailOK m b (D - 1) outA srcs = true) : (liftGraph n m outA).ediam = D := by
  apply le_antisymm
  · rw [SimpleGraph.ediam_le_iff]; exact hle
  · obtain ⟨v, w, hvw⟩ := exists_far hn hm hA hS hF
    have h1 : ((D - 1 : ℕ) : ℕ∞) < (liftGraph n m outA).edist v w := lt_of_not_ge hvw
    have h2 : ((D : ℕ) : ℕ∞) ≤ (liftGraph n m outA).edist v w := by
      have : ((D - 1 : ℕ) : ℕ∞) + 1 = (D : ℕ∞) := by
        exact_mod_cast Nat.sub_add_cancel hD
      rw [← this]
      exact Order.add_one_le_of_lt h1
    exact h2.trans (SimpleGraph.edist_le_ediam)

end Complete

section Regular

variable {n m b d : ℕ} {outA : List (List (ℕ × ℕ))}

/-- The neighbour list of a vertex has no repeats and does not contain the vertex. -/
theorem nbrs_nodup (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true)
    (hR : regOK d b outA = true) (v : Fin n) : (nbrs n m outA v).Nodup := by
  have hv := div_lt_of_fin hn v
  have hnd : (outA.getD (v.val / m) []).Nodup := by
    have := List.all_eq_true.mp hR (v.val / m) (List.mem_range.mpr hv)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2
  unfold nbrs
  apply hnd.map_on
  intro p hp q hq hpq
  obtain ⟨hp1, hp2⟩ := of_arcsOK hA hv hp
  obtain ⟨hq1, hq2⟩ := of_arcsOK hA hv hq
  have hpl : p.1 * m + (v.val % m + p.2) % m < n :=
    lt_of_lt_of_eq (lt_mul_of_lt hp1 (Nat.mod_lt _ hm)) hn.symm
  have hql : q.1 * m + (v.val % m + q.2) % m < n :=
    lt_of_lt_of_eq (lt_mul_of_lt hq1 (Nat.mod_lt _ hm)) hn.symm
  have hval := congrArg Fin.val hpq
  simp only [Nat.mod_eq_of_lt hpl, Nat.mod_eq_of_lt hql] at hval
  have e1 := div_mod_of_lt (u := p.1) (Nat.mod_lt (v.val % m + p.2) hm)
  have e2 := div_mod_of_lt (u := q.1) (Nat.mod_lt (v.val % m + q.2) hm)
  have h1 : p.1 = q.1 := by rw [← e1.1, ← e2.1, hval]
  have h2 : (v.val % m + p.2) % m = (v.val % m + q.2) % m := by rw [← e1.2, ← e2.2, hval]
  -- `x + β` mod `m` determines `β < m`
  have h3 : p.2 = q.2 := by
    have hx := Nat.mod_lt v.val hm
    have k1 : off m (v.val % m) ((v.val % m + p.2) % m) = p.2 := by
      rw [off_step hx, off_self, Nat.zero_add, Nat.mod_eq_of_lt hp2]
    have k2 : off m (v.val % m) ((v.val % m + q.2) % m) = q.2 := by
      rw [off_step hx, off_self, Nat.zero_add, Nat.mod_eq_of_lt hq2]
    rw [← k1, ← k2, h2]
  exact Prod.ext h1 h3

theorem not_mem_nbrs_self (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true)
    {side : List Bool} (hc : colOK b side outA = true) (v : Fin n) : v ∉ nbrs n m outA v := by
  intro h
  obtain ⟨p, hp, hval⟩ := val_of_mem_nbrs hn hm hA h
  have hv := div_lt_of_fin hn v
  have hpv : p.1 = v.val / m := by
    have := (div_mod_of_lt (u := p.1) (Nat.mod_lt (v.val % m + p.2) hm)).1
    rw [← hval] at this; exact this.symm
  have := List.all_eq_true.mp (List.all_eq_true.mp hc (v.val / m) (List.mem_range.mpr hv)) p hp
  simp only [hpv, bne_self_eq_false] at this
  exact Bool.noConfusion this

/-- Every vertex has exactly `d` neighbours. -/
theorem ncard_neighborSet_eq (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true)
    (hS : symOK m b outA = true) {side : List Bool} (hc : colOK b side outA = true)
    (hR : regOK d b outA = true) (v : Fin n) : ((liftGraph n m outA).neighborSet v).ncard = d := by
  have hset : (liftGraph n m outA).neighborSet v = ↑(nbrs n m outA v).toFinset := by
    ext w
    rw [SimpleGraph.mem_neighborSet]
    simp only [Finset.mem_coe, List.mem_toFinset, liftGraph, graphOf, SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨-, h | h⟩
      · exact h
      · exact mem_nbrs_symm hn hm hA hS h
    · intro h
      refine ⟨fun hvw => ?_, Or.inl h⟩
      subst hvw
      exact not_mem_nbrs_self hn hm hA hc v h
  have hv := div_lt_of_fin hn v
  have hlen : (outA.getD (v.val / m) []).length = d := by
    have := List.all_eq_true.mp hR (v.val / m) (List.mem_range.mpr hv)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup (nbrs_nodup hn hm hA hR v)]
  simp only [nbrs, List.length_map, hlen]

end Regular

/-- Exact degree and exact diameter, from the upper bounds and the extra checks. -/
theorem exact_of {n m b d D : ℕ} {outA : List (List (ℕ × ℕ))} (side : List Bool) (srcs : List ℕ)
    (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true) (hS : symOK m b outA = true)
    (hc : colOK b side outA = true) (hR : regOK d b outA = true) (hD : 0 < D)
    (hB : IsBipartiteDegDiam (liftGraph n m outA) d D) (hF : eccFailOK m b (D - 1) outA srcs = true) :
    (∀ v, ((liftGraph n m outA).neighborSet v).ncard = d) ∧ (liftGraph n m outA).ediam = D :=
  ⟨ncard_neighborSet_eq hn hm hA hS hc hR,
    ediam_eq_of hn hm hA hS hD (SimpleGraph.ediam_le_iff.mp hB.2.2) hF⟩

end BipartiteDD.CycLift
