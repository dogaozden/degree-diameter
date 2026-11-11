import BipartiteDD.Basic

/-! Regular cyclic voltage lifts, and a diameter check that runs one breadth-first search per base vertex.

A base graph on the vertices `0, …, b - 1` is given by its arc lists: `outA.getD w []` lists the pairs `(u, β)`,
one for each arc `w → u`, with voltage `β ∈ Z_m`. The lift has the vertices `u * m + y` (`u < b`, `y < m`), and
vertex `(w, x)` has the neighbours `(u, (x + β) % m)` for the arcs `(u, β)` out of `w` (`nbrs`). The graph is
`graphOf nbrs`, as in `Basic`.

The rotation `x ↦ x + 1` of every fibre is an automorphism of such a lift, so the distance from `(u₀, x)` to
`(w, y)` depends only on `u₀`, `w` and `y - x`. The search below uses this directly: for each base vertex `u₀` it
keeps one `m`-bit mask per base vertex `w`, where bit `z` of the mask of `w` at radius `r` says that every
`(w, x + z)` is within `r` steps of `(u₀, x)`, for all `x` at once (`bfs_sound`). One radius step ORs, into the
mask of `w`, the mask of each out-neighbour `u` rotated back by the arc's voltage (`stepM`, `rotR`). So the whole
diameter check is `b` searches of `D` steps on `b` masks of `m` bits, with no all-pairs table.

`isBipartiteDegDiam_of_checks` turns five Boolean checks on the base data into `IsBipartiteDegDiam`. -/

namespace BipartiteDD.CycLift

open BipartiteDD

/-! ### Masks -/

/-- Rotate an `m`-bit mask right by `β`: bit `y` of the result is bit `(y + β) % m` of `x` (`testBit_rotR`).
Bits of `x` at `m` and above are ignored. -/
def rotR (m β x : ℕ) : ℕ :=
  ((x &&& (2 ^ m - 1)) >>> β ||| (x &&& (2 ^ m - 1)) <<< (m - β)) &&& (2 ^ m - 1)

theorem testBit_rotR {m β x y : ℕ} (hβ : β < m) (hy : y < m) :
    (rotR m β x).testBit y = x.testBit ((y + β) % m) := by
  unfold rotR
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    Nat.testBit_two_pow_sub_one]
  by_cases h : y + β < m
  · rw [Nat.mod_eq_of_lt h]
    have h1 : ¬ (y ≥ m - β) := by omega
    simp [h, hy, h1, Nat.add_comm β y]
  · have h2 : (y + β) % m = y + β - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [h2]
    have h1 : y ≥ m - β := by omega
    have h3 : ¬ (β + y < m) := by omega
    have h4 : y - (m - β) = y + β - m := by omega
    have h5 : y + β - m < m := by omega
    simp [h3, hy, h1, h4, h5]

/-! ### The search -/

/-- One radius step. `cur.getD w 0` is the mask of the base vertex `w`. The new mask of `w` is the old one, ORed
with the mask of `u` rotated back by `β` for every arc `(u, β)` out of `w`. -/
def stepM (m b : ℕ) (outA : List (List (ℕ × ℕ))) (cur : List ℕ) : List ℕ :=
  (List.range b).map fun w =>
    (outA.getD w []).foldl (fun acc p => acc ||| rotR m p.2 (cur.getD p.1 0)) (cur.getD w 0)

/-- The masks at radius `r` of the search from the base vertex `u₀`. At radius `0` only voltage `0` at `u₀`. -/
def levM (m b : ℕ) (outA : List (List (ℕ × ℕ))) (u₀ : ℕ) : ℕ → List ℕ
  | 0 => (List.range b).map fun w => if w = u₀ then 1 else 0
  | r + 1 => stepM m b outA (levM m b outA u₀ r)

/-- Every search ends, at radius `D`, with all `m` bits set at every base vertex. -/
def eccOK (m b D : ℕ) (outA : List (List (ℕ × ℕ))) : Bool :=
  (List.range b).all fun u₀ =>
    (levM m b outA u₀ D).all fun x => (x &&& (2 ^ m - 1)) == 2 ^ m - 1

/-- Every arc stays inside the base and has a voltage below `m`. -/
def arcsOK (m b : ℕ) (outA : List (List (ℕ × ℕ))) : Bool :=
  (List.range b).all fun w => (outA.getD w []).all fun p => decide (p.1 < b) && decide (p.2 < m)

/-- Every arc `w → u` with voltage `β` has the reverse arc `u → w` with voltage `(m - β) % m`. -/
def symOK (m b : ℕ) (outA : List (List (ℕ × ℕ))) : Bool :=
  (List.range b).all fun w => (outA.getD w []).all fun p => (outA.getD p.1 []).contains (w, (m - p.2) % m)

/-- Every base vertex has at most `d` arcs. -/
def degOK (d b : ℕ) (outA : List (List (ℕ × ℕ))) : Bool :=
  (List.range b).all fun w => decide ((outA.getD w []).length ≤ d)

/-- `side` is a proper 2-colouring of the base graph. -/
def colOK (b : ℕ) (side : List Bool) (outA : List (List (ℕ × ℕ))) : Bool :=
  (List.range b).all fun w => (outA.getD w []).all fun p => side.getD w false != side.getD p.1 false

/-! ### The lift -/

/-- Neighbours of the vertex `v = w * m + x` of the lift: `(u, (x + β) % m)` for each arc `(u, β)` out of `w`. -/
def nbrs (n m : ℕ) (outA : List (List (ℕ × ℕ))) (v : Fin n) : List (Fin n) :=
  (outA.getD (v.val / m) []).map fun p =>
    ⟨(p.1 * m + (v.val % m + p.2) % m) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) v.isLt)⟩

/-- The lift as a simple graph. -/
def liftGraph (n m : ℕ) (outA : List (List (ℕ × ℕ))) : SimpleGraph (Fin n) :=
  graphOf (nbrs n m outA)

section Facts

variable {n m b : ℕ} {outA : List (List (ℕ × ℕ))}

theorem of_arcsOK (h : arcsOK m b outA = true) {w : ℕ} (hw : w < b) {p : ℕ × ℕ}
    (hp : p ∈ outA.getD w []) : p.1 < b ∧ p.2 < m := by
  have := List.all_eq_true.mp (List.all_eq_true.mp h w (List.mem_range.mpr hw)) p hp
  simpa using this

theorem val_lt_of_fin (hn : n = b * m) (v : Fin n) : v.val < b * m := lt_of_lt_of_eq v.isLt hn

theorem div_lt_of_fin (hn : n = b * m) (v : Fin n) : v.val / m < b :=
  Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact val_lt_of_fin hn v)

/-- `u * m + y < b * m` for `u < b` and `y < m`. -/
theorem lt_mul_of_lt {m b u y : ℕ} (hu : u < b) (hy : y < m) : u * m + y < b * m :=
  calc u * m + y < u * m + m := Nat.add_lt_add_left hy _
    _ = (u + 1) * m := (Nat.succ_mul u m).symm
    _ ≤ b * m := Nat.mul_le_mul_right m hu

/-- The value of a neighbour, without the outer `% n`. -/
theorem val_of_mem_nbrs (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true) {v w : Fin n}
    (h : w ∈ nbrs n m outA v) :
    ∃ p ∈ outA.getD (v.val / m) [], w.val = p.1 * m + (v.val % m + p.2) % m := by
  simp only [nbrs, List.mem_map] at h
  obtain ⟨p, hp, rfl⟩ := h
  refine ⟨p, hp, ?_⟩
  have hp1 := (of_arcsOK hA (div_lt_of_fin hn v) hp).1
  have hlt : p.1 * m + (v.val % m + p.2) % m < n :=
    lt_of_lt_of_eq (lt_mul_of_lt hp1 (Nat.mod_lt _ hm)) hn.symm
  exact Nat.mod_eq_of_lt hlt

/-- Division and remainder of `u * m + y` for `y < m`. -/
theorem div_mod_of_lt {m u y : ℕ} (hy : y < m) : (u * m + y) / m = u ∧ (u * m + y) % m = y := by
  have hm : 0 < m := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hy, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]

/-- The neighbour of `v` along an arc `p` out of `v / m`. -/
theorem mem_nbrs_of_arc (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true) (v : Fin n)
    {p : ℕ × ℕ} (hp : p ∈ outA.getD (v.val / m) []) :
    ∃ w ∈ nbrs n m outA v, w.val / m = p.1 ∧ w.val % m = (v.val % m + p.2) % m := by
  have hlt : p.1 * m + (v.val % m + p.2) % m < n := by
    have hp1 := (of_arcsOK hA (div_lt_of_fin hn v) hp).1
    exact lt_of_lt_of_eq (lt_mul_of_lt hp1 (Nat.mod_lt _ hm)) hn.symm
  refine ⟨⟨p.1 * m + (v.val % m + p.2) % m, hlt⟩, ?_, ?_⟩
  · simp only [nbrs, List.mem_map]
    exact ⟨p, hp, Fin.ext (Nat.mod_eq_of_lt hlt)⟩
  · exact div_mod_of_lt (Nat.mod_lt _ hm)

/-- A vertex is determined by its base vertex and its fibre coordinate. -/
theorem fin_eq_of_div_mod {v w : Fin n} (h1 : v.val / m = w.val / m) (h2 : v.val % m = w.val % m) :
    v = w := by
  apply Fin.ext
  rw [← Nat.div_add_mod v.val m, ← Nat.div_add_mod w.val m, h1, h2]

end Facts

/-! ### Soundness of the search -/

/-- A bit is set in a fold of ORs iff it is set in the start value or in one of the terms. -/
theorem testBit_foldl_or' {α : Type} (l : List α) (f : α → ℕ) (init i : ℕ) :
    (l.foldl (fun acc p => acc ||| f p) init).testBit i = true ↔
      init.testBit i = true ∨ ∃ p ∈ l, (f p).testBit i = true := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, List.mem_cons, exists_eq_or_imp,
      Bool.or_eq_true]
    tauto

theorem length_levM (m b : ℕ) (outA : List (List (ℕ × ℕ))) (u₀ r : ℕ) :
    (levM m b outA u₀ r).length = b := by
  cases r <;> simp [levM, stepM]

/-- The fibre offset `(y - x) mod m`, written for naturals `x, y < m`. -/
def off (m x y : ℕ) : ℕ := (y + m - x) % m

theorem off_step {m x y β : ℕ} (hx : x < m) : off m x ((y + β) % m) = (off m x y + β) % m := by
  unfold off
  have e1 : (y + β) % m + m - x = (y + β) % m + (m - x) := by omega
  have e2 : y + m - x = y + (m - x) := by omega
  rw [e1, e2, Nat.mod_add_mod, Nat.mod_add_mod]
  congr 1
  omega

theorem off_self {m x : ℕ} : off m x x = 0 := by
  unfold off
  have : x + m - x = m := by omega
  rw [this, Nat.mod_self]

theorem eq_of_off_zero {m x y : ℕ} (hx : x < m) (hy : y < m) (h : off m x y = 0) : x = y := by
  unfold off at h
  by_cases hxy : x ≤ y
  · have e : y + m - x = (y - x) + m := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at h
    omega

/-- What the search proves: if bit `off m (v % m) (w % m)` of the mask of `w / m` is set at radius `r` of the
search from `v / m`, then `w` is within `r` steps of `v`. -/
theorem bfs_sound (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true) (v : Fin n) :
    ∀ (r : ℕ) (w : Fin n),
      ((levM m b outA (v.val / m) r).getD (w.val / m) 0).testBit (off m (v.val % m) (w.val % m)) = true →
      (liftGraph n m outA).edist v w ≤ r := by
  intro r
  induction r with
  | zero =>
    intro w h
    have hw := div_lt_of_fin hn w
    simp only [levM, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hw,
      Option.map_some, Option.getD_some] at h
    by_cases hu : w.val / m = v.val / m
    · simp only [hu, ↓reduceIte, Nat.testBit_one_eq_true_iff_self_eq_zero] at h
      have hx := eq_of_off_zero (Nat.mod_lt v.val hm) (Nat.mod_lt w.val hm) h
      have : v = w := fin_eq_of_div_mod hu.symm hx
      subst this
      simp
    · simp [hu] at h
  | succ r ih =>
    intro w h
    have hw := div_lt_of_fin hn w
    have hlev : levM m b outA (v.val / m) (r + 1) =
        stepM m b outA (levM m b outA (v.val / m) r) := rfl
    rw [hlev] at h
    simp only [stepM, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hw,
      Option.map_some, Option.getD_some] at h
    simp only [← List.getD_eq_getElem?_getD] at h
    rw [testBit_foldl_or'] at h
    rcases h with h | ⟨p, hp, hbit⟩
    · exact (ih w h).trans (by exact_mod_cast Nat.le_succ r)
    · obtain ⟨hp1, hp2⟩ := of_arcsOK hA hw hp
      obtain ⟨w', hw'mem, hw'1, hw'2⟩ := mem_nbrs_of_arc hn hm hA w hp
      have hoff : off m (v.val % m) (w.val % m) < m := Nat.mod_lt _ hm
      rw [testBit_rotR hp2 hoff] at hbit
      have hih : (liftGraph n m outA).edist v w' ≤ r := by
        apply ih
        rw [hw'1, hw'2, off_step (Nat.mod_lt _ hm)]
        exact hbit
      have hadj : (liftGraph n m outA).edist w' w ≤ 1 := by
        rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
        by_cases hww : w' = w
        · exact Or.inr hww
        · refine Or.inl ?_
          simp only [liftGraph, graphOf, SimpleGraph.fromRel_adj]
          exact ⟨hww, Or.inr hw'mem⟩
      calc (liftGraph n m outA).edist v w
          ≤ (liftGraph n m outA).edist v w' + (liftGraph n m outA).edist w' w :=
            SimpleGraph.edist_triangle
        _ ≤ r + 1 := add_le_add hih hadj
        _ = ((r + 1 : ℕ) : ℕ∞) := by push_cast; rfl

/-- If every search is full at radius `D`, every two vertices are within `D` steps. -/
theorem edist_le_of_eccOK (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true)
    {D : ℕ} (hE : eccOK m b D outA = true) (v w : Fin n) : (liftGraph n m outA).edist v w ≤ D := by
  apply bfs_sound hn hm hA v D w
  have hv := div_lt_of_fin hn v
  have hw := div_lt_of_fin hn w
  have hall := List.all_eq_true.mp hE (v.val / m) (List.mem_range.mpr hv)
  have hlen := length_levM m b outA (v.val / m) D
  have hmem : (levM m b outA (v.val / m) D).getD (w.val / m) 0 ∈ levM m b outA (v.val / m) D := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hw),
      Option.getD_some]
    exact List.getElem_mem _
  have hx := List.all_eq_true.mp hall _ hmem
  simp only [beq_iff_eq] at hx
  have hoff : off m (v.val % m) (w.val % m) < m := Nat.mod_lt _ hm
  have := congrArg (fun z => Nat.testBit z (off m (v.val % m) (w.val % m))) hx
  simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_one, hoff, decide_true, Bool.and_true] at this
  exact this

/-! ### The local part: degree and colouring -/

section Local

variable {n m b d : ℕ} {outA : List (List (ℕ × ℕ))}

theorem off_inv {m x β : ℕ} (hx : x < m) (hβ : β < m) : ((x + β) % m + (m - β) % m) % m = x := by
  rw [Nat.add_mod_mod, Nat.mod_add_mod]
  have : x + β + (m - β) = x + m := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hx]

/-- With `symOK`, every neighbour `w` of `v` has `v` in its own list. -/
theorem mem_nbrs_symm (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true)
    (hS : symOK m b outA = true) {v w : Fin n} (h : w ∈ nbrs n m outA v) : v ∈ nbrs n m outA w := by
  obtain ⟨p, hp, hwv⟩ := val_of_mem_nbrs hn hm hA h
  have hv := div_lt_of_fin hn v
  obtain ⟨hp1, hp2⟩ := of_arcsOK hA hv hp
  have hwd : w.val / m = p.1 ∧ w.val % m = (v.val % m + p.2) % m := by
    rw [hwv]; exact div_mod_of_lt (Nat.mod_lt _ hm)
  have hrev : (v.val / m, (m - p.2) % m) ∈ outA.getD (w.val / m) [] := by
    have := List.all_eq_true.mp (List.all_eq_true.mp hS (v.val / m) (List.mem_range.mpr hv)) p hp
    rw [hwd.1]
    simpa using this
  obtain ⟨v', hv'mem, hv'1, hv'2⟩ := mem_nbrs_of_arc hn hm hA w hrev
  have : v' = v := by
    apply fin_eq_of_div_mod hv'1
    rw [hv'2, hwd.2]
    exact off_inv (Nat.mod_lt _ hm) hp2
  rw [← this]
  exact hv'mem

/-- Adjacent vertices lie over an arc of the base. -/
theorem arc_of_adj (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true) {v w : Fin n}
    (h : (liftGraph n m outA).Adj v w) :
    (∃ p ∈ outA.getD (v.val / m) [], p.1 = w.val / m) ∨
      (∃ p ∈ outA.getD (w.val / m) [], p.1 = v.val / m) := by
  simp only [liftGraph, graphOf, SimpleGraph.fromRel_adj] at h
  rcases h.2 with h | h
  · obtain ⟨p, hp, hval⟩ := val_of_mem_nbrs hn hm hA h
    refine Or.inl ⟨p, hp, ?_⟩
    rw [hval]; exact (div_mod_of_lt (Nat.mod_lt _ hm)).1.symm
  · obtain ⟨p, hp, hval⟩ := val_of_mem_nbrs hn hm hA h
    refine Or.inr ⟨p, hp, ?_⟩
    rw [hval]; exact (div_mod_of_lt (Nat.mod_lt _ hm)).1.symm

end Local

/-- The four local checks on the base data and a bound on all distances give `IsBipartiteDegDiam`. -/
theorem isBipartiteDegDiam_of_edist {n m b d D : ℕ} {outA : List (List (ℕ × ℕ))} (side : List Bool)
    (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true) (hS : symOK m b outA = true)
    (hd : degOK d b outA = true) (hc : colOK b side outA = true)
    (hdiam : ∀ v w : Fin n, (liftGraph n m outA).edist v w ≤ D) :
    IsBipartiteDegDiam (liftGraph n m outA) d D := by
  refine ⟨?_, ?_, ?_⟩
  · let C : (liftGraph n m outA).Coloring (Fin 2) :=
      SimpleGraph.Coloring.mk (fun v => if side.getD (v.val / m) false then 1 else 0) (by
        intro v w hvw
        have hv := div_lt_of_fin hn v
        have hw := div_lt_of_fin hn w
        have hne : side.getD (v.val / m) false ≠ side.getD (w.val / m) false := by
          rcases arc_of_adj hn hm hA hvw with ⟨p, hp, hpw⟩ | ⟨p, hp, hpv⟩
          · have := List.all_eq_true.mp (List.all_eq_true.mp hc (v.val / m) (List.mem_range.mpr hv)) p hp
            rw [← hpw]
            simpa using this
          · have := List.all_eq_true.mp (List.all_eq_true.mp hc (w.val / m) (List.mem_range.mpr hw)) p hp
            rw [← hpv]
            simp only [bne_iff_ne, ne_eq] at this
            exact fun h => this h.symm
        by_cases h1 : side.getD (v.val / m) false <;> by_cases h2 : side.getD (w.val / m) false <;>
          simp_all)
    exact ⟨C⟩
  · intro v
    have hsub : (liftGraph n m outA).neighborSet v ⊆ ↑(nbrs n m outA v).toFinset := by
      intro w hw
      rw [SimpleGraph.mem_neighborSet] at hw
      simp only [Finset.mem_coe, List.mem_toFinset]
      simp only [liftGraph, graphOf, SimpleGraph.fromRel_adj] at hw
      rcases hw.2 with h | h
      · exact h
      · exact mem_nbrs_symm hn hm hA hS h
    have hv := div_lt_of_fin hn v
    have hdeg : (outA.getD (v.val / m) []).length ≤ d := by
      have := List.all_eq_true.mp hd (v.val / m) (List.mem_range.mpr hv)
      simpa using this
    calc ((liftGraph n m outA).neighborSet v).ncard
        ≤ (((nbrs n m outA v).toFinset : Finset (Fin n)) : Set (Fin n)).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = (nbrs n m outA v).toFinset.card := Set.ncard_coe_finset _
      _ ≤ (nbrs n m outA v).length := List.toFinset_card_le _
      _ = (outA.getD (v.val / m) []).length := by simp [nbrs]
      _ ≤ d := hdeg
  · rw [SimpleGraph.ediam_le_iff]
    exact hdiam

/-- The main theorem: the five checks on the base data give a bipartite lift of degree at most `d` and diameter
at most `D`. -/
theorem isBipartiteDegDiam_of_checks {n m b d D : ℕ} {outA : List (List (ℕ × ℕ))} (side : List Bool)
    (hn : n = b * m) (hm : 0 < m) (hA : arcsOK m b outA = true) (hS : symOK m b outA = true)
    (hd : degOK d b outA = true) (hc : colOK b side outA = true) (hE : eccOK m b D outA = true) :
    IsBipartiteDegDiam (liftGraph n m outA) d D :=
  isBipartiteDegDiam_of_edist side hn hm hA hS hd hc (edist_le_of_eccOK hn hm hA hE)

end BipartiteDD.CycLift
