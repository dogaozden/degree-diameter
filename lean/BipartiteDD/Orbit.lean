import BipartiteDD.StagedLocal

/-! # Orbit reduction for cyclic fibre lifts

Let `τ` be a map on the vertices of a graph `G` that preserves adjacency, with `τ^[m] = id`.
Suppose `rep i` (for `i` in some index type) are vertices such that every vertex `u` is `τ^[j] (rep i)`
for some `i` and some `j < m`. If every `rep i` is within `D` of every vertex, then `G` has diameter
at most `D`. The reason: `u = τ^[j] (rep i)`, and `τ^[j]` preserves distances, so
`dist u v = dist (rep i) (τ^[m-j] v)` for the suitable `τ^[m-j]`-image of `v`.

Only the representatives need a ball check. For a lift whose fibres are the orbits of `τ`
(vertex `m x + h` in fibre `x`, and `τ` adds `1` to `h` modulo `m`), the representatives are the `k = n / m`
vertices `m x`. The ball data is then one `k`-bit mask per vertex and radius: bit `i` of the mask of `v`
at radius `r` says that `m i` is within `r` of `v`. A step of the masks is the ordinary staged step
(`Fast.step`), so the `Staged` machinery applies unchanged, with masks of `k` bits instead of `n`.

Files in this module:
* the orbit lemma (`ediam_le_of_orbits`) for any graph and any adjacency-preserving `τ`;
* the chain soundness (`edist_le_of_chain`): bit `i` of level `r` at `v` gives `dist (rv i) v ≤ r`;
* the cyclic shift `shiftN` with its fibre formulas, and `homOK`, the Bool check that `shiftN` preserves
  adjacency on the given lists;
* `lift_sound`: from the staged data and the checks, `∃ G, IsBipartiteDegDiam G d D`. -/

namespace BipartiteDD.Orbit

open BipartiteDD BipartiteDD.Fast BipartiteDD.Staged

/-! ## 1. Adjacency-preserving maps and the orbit lemma -/

section Hom

variable {V : Type*}

/-- `σ` maps adjacent vertices to adjacent vertices. -/
def IsHom (G : SimpleGraph V) (σ : V → V) : Prop :=
  ∀ x y, G.Adj x y → G.Adj (σ x) (σ y)

theorem IsHom.iterate {G : SimpleGraph V} {σ : V → V} (h : IsHom G σ) (j : ℕ) :
    IsHom G (σ^[j]) := by
  induction j with
  | zero => exact fun _ _ hxy => hxy
  | succ j ih =>
    intro x y hxy
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact h _ _ (ih x y hxy)

/-- An adjacency-preserving map does not increase distances. -/
theorem edist_le_edist_of_isHom {G : SimpleGraph V} {σ : V → V} (h : IsHom G σ) (x y : V) :
    G.edist (σ x) (σ y) ≤ G.edist x y := by
  by_cases hr : G.Reachable x y
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
    let f : G →g G := ⟨σ, fun {a b} hab => h a b hab⟩
    calc G.edist (σ x) (σ y) ≤ ((p.map f).length : ℕ∞) := SimpleGraph.edist_le _
      _ = (p.length : ℕ∞) := by rw [SimpleGraph.Walk.length_map]
      _ = G.edist x y := by rw [hp]
  · rw [SimpleGraph.edist_eq_top_of_not_reachable hr]
    exact le_top

/-- The orbit lemma. Every vertex is `τ^[j] (rep i)` with `j < m`, and every representative is within `D`
of every vertex; then the diameter is at most `D`. -/
theorem ediam_le_of_orbits {G : SimpleGraph V} {τ : V → V} (hτ : IsHom G τ) {m : ℕ}
    (hm : ∀ v, τ^[m] v = v) {ι : Type*} (rep : ι → V) {D : ℕ}
    (hrep : ∀ i w, G.edist (rep i) w ≤ D) (hcov : ∀ u, ∃ i, ∃ j < m, τ^[j] (rep i) = u) :
    G.ediam ≤ D := by
  rw [SimpleGraph.ediam_le_iff]
  intro u v
  obtain ⟨i, j, hj, rfl⟩ := hcov u
  have hsum : j + (m - j) = m := by omega
  have h2 : τ^[j] (τ^[m - j] v) = v := by
    rw [← Function.iterate_add_apply, hsum, hm]
  have h1 := edist_le_edist_of_isHom (hτ.iterate j) (rep i) (τ^[m - j] v)
  rw [h2] at h1
  exact h1.trans (hrep i _)

end Hom

/-! ## 2. Masks along a chain of staged steps -/

/-- The graph of a neighbour-list table. -/
abbrev gOf {n : ℕ} (adj : List (List (Fin n))) : SimpleGraph (Fin n) :=
  graphOf fun u : Fin n => adj.getD u.val []

/-- Level 0 of the masks of the representatives: `v` carries bit `v / m` when `m ∣ v`. -/
def repLevel0 (m n : ℕ) : List ℕ :=
  (List.range n).map fun v => if v % m = 0 then 2 ^ (v / m) else 0

/-- One step of a list of masks, at one vertex, in the form of `Basic.ball`: the mask at `v` is the OR of
the masks of `v` and its neighbours. -/
theorem levels_getD_succ {n K : ℕ} (adj : List (List (Fin n))) (hK : n ≤ 2 ^ K) (cur : List ℕ)
    (v : Fin n) :
    (step K (Tree.build [] K adj) cur).getD v.val 0 =
      (adj.getD v.val []).foldl (fun acc u => acc ||| cur.getD u.val 0) (cur.getD v.val 0) := by
  simp only [step_getD, get_build_fin hK]

/-- Chain soundness. `L 0` is the start list, `L (r + 1)` the step of `L r`. If bit `i` is set at `v` in
level `r`, then the representative `rv i` is within `r` steps of `v`. -/
theorem edist_le_of_chain {n K D : ℕ} (adj : List (List (Fin n))) (hK : n ≤ 2 ^ K)
    (rv : ℕ → Fin n) (L : ℕ → List ℕ)
    (h0 : ∀ (i : ℕ) (v : Fin n), ((L 0).getD v.val 0).testBit i = true → rv i = v)
    (hs : ∀ r < D, step K (Tree.build [] K adj) (L r) = L (r + 1)) :
    ∀ r ≤ D, ∀ (i : ℕ) (v : Fin n), ((L r).getD v.val 0).testBit i = true →
      (gOf adj).edist (rv i) v ≤ r := by
  intro r
  induction r with
  | zero =>
    intro _ i v h
    rw [h0 i v h, SimpleGraph.edist_self]
    simp
  | succ r ih =>
    intro hr i v h
    rw [← hs r (by omega), levels_getD_succ adj hK] at h
    rcases (testBit_foldl_or (adj.getD v.val []) (fun u : Fin n => (L r).getD u.val 0)
        ((L r).getD v.val 0) i).mp h with h | ⟨u, hu, hw⟩
    · exact (ih (by omega) i v h).trans (by exact_mod_cast Nat.le_succ r)
    · have hadj : (gOf adj).edist u v ≤ 1 := by
        rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
        by_cases huv : u = v
        · exact Or.inr huv
        · refine Or.inl ?_
          simp only [gOf, graphOf, SimpleGraph.fromRel_adj]
          exact ⟨huv, Or.inr hu⟩
      calc (gOf adj).edist (rv i) v
          ≤ (gOf adj).edist (rv i) u + (gOf adj).edist u v := SimpleGraph.edist_triangle
        _ ≤ (r : ℕ∞) + 1 := add_le_add (ih (by omega) i u hw) hadj
        _ = ((r + 1 : ℕ) : ℕ∞) := by push_cast; rfl

/-! ## 3. Local test, bridged to the neighbour-list graph -/

/-- The local test of `Staged.checkLocal`, read per vertex. -/
theorem local_spec {n K d : ℕ} (adj : List (List (Fin n))) (col : List Bool) (hK : n ≤ 2 ^ K)
    (hloc : checkLocal K d adj col = true) :
    ∀ u : Fin n, (adj.getD u.val []).length ≤ d ∧
      ∀ v ∈ adj.getD u.val [], u ∈ adj.getD v.val [] ∧
        col.getD u.val false ≠ col.getD v.val false := by
  intro u
  have hu := (List.all_eq_true.mp hloc) u.val (List.mem_range.mpr u.isLt)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.any_eq_true,
    bne_iff_ne, ne_eq] at hu
  obtain ⟨h1, h2⟩ := hu
  have hadj : ∀ v : Fin n, Tree.get [] K (Tree.build [] K adj) v.val = adj.getD v.val [] :=
    fun v => get_build_fin hK _ _ v
  have hcol : ∀ v : Fin n, Tree.get false K (Tree.build false K col) v.val = col.getD v.val false :=
    fun v => get_build_fin hK _ _ v
  simp only [hadj, hcol] at h1 h2
  refine ⟨h1, fun v hv => ?_⟩
  obtain ⟨⟨w, hw, hwu⟩, hc⟩ := h2 v hv
  have hwu' : w = u := Fin.ext hwu
  subst hwu'
  exact ⟨hw, hc⟩

/-- Two adjacent vertex ranges with the local test give their union. -/
theorem checkLocalRange_append {K d n : ℕ} {adj : List (List (Fin n))} {col : List Bool}
    {lo m cnt : ℕ} (h1 : checkLocalRange K d adj col lo m = true)
    (h2 : checkLocalRange K d adj col (lo + m) cnt = true) :
    checkLocalRange K d adj col lo (m + cnt) = true := by
  unfold checkLocalRange at h1 h2 ⊢
  rw [← List.range'_append, List.all_append]
  rw [h1, Bool.true_and]
  simpa [Nat.one_mul] using h2

/-- `checkLocalRange_append` with the offsets and totals given as equations, so that the arguments unify
syntactically (Nat literal arithmetic inside `checkLocalRange` otherwise hits the recursion limit). -/
theorem checkLocalRange_join {K d n : ℕ} {adj : List (List (Fin n))} {col : List Bool}
    {lo m cnt lo2 tot : ℕ} (hl : lo + m = lo2) (hc : m + cnt = tot)
    (h1 : checkLocalRange K d adj col lo m = true)
    (h2 : checkLocalRange K d adj col lo2 cnt = true) :
    checkLocalRange K d adj col lo tot = true := by
  subst hl
  subst hc
  exact checkLocalRange_append h1 h2

/-- A neighbour-list table with the per-vertex local test is a bipartite graph of degree at most `d`
whose diameter is at most `D` as soon as `ediam ≤ D`. -/
theorem isBipartiteDegDiam_of_local {n : ℕ} (adj : List (List (Fin n))) (color : Fin n → Bool)
    (d D : ℕ)
    (hloc : ∀ u : Fin n, (adj.getD u.val []).length ≤ d ∧
      ∀ v ∈ adj.getD u.val [], u ∈ adj.getD v.val [] ∧ color u ≠ color v)
    (hdiam : (gOf adj).ediam ≤ D) : IsBipartiteDegDiam (gOf adj) d D := by
  have hmem : ∀ {u v : Fin n}, (gOf adj).Adj u v → v ∈ adj.getD u.val [] := by
    intro u v h
    simp only [gOf, graphOf, SimpleGraph.fromRel_adj] at h
    rcases h.2 with h | h
    · exact h
    · exact ((hloc v).2 u h).1
  have hcolor : ∀ {u v : Fin n}, (gOf adj).Adj u v → color u ≠ color v := by
    intro u v h
    exact ((hloc u).2 v (hmem h)).2
  refine ⟨?_, ?_, hdiam⟩
  · refine ⟨SimpleGraph.Coloring.mk (fun v => if color v then (1 : Fin 2) else 0) ?_⟩
    intro v w hvw
    have hc := hcolor hvw
    by_cases hv : color v <;> by_cases hw : color w <;> simp_all
  · intro v
    have hsub : (gOf adj).neighborSet v ⊆ ↑(adj.getD v.val []).toFinset := by
      intro w hw
      rw [SimpleGraph.mem_neighborSet] at hw
      simp only [Finset.mem_coe, List.mem_toFinset]
      exact hmem hw
    calc ((gOf adj).neighborSet v).ncard
        ≤ (((adj.getD v.val []).toFinset : Finset (Fin n)) : Set (Fin n)).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = (adj.getD v.val []).toFinset.card := Set.ncard_coe_finset _
      _ ≤ (adj.getD v.val []).length := List.toFinset_card_le _
      _ ≤ d := (hloc v).1

/-! ## 4. The cyclic fibre shift -/

/-- The fibre shift: in fibre `x` (the numbers `m x, …, m x + m - 1`), `h ↦ h + 1 (mod m)`. -/
def shiftN (m v : ℕ) : ℕ := m * (v / m) + (v % m + 1) % m

theorem shiftN_fib {m x g : ℕ} (hm : 0 < m) (hg : g < m) :
    shiftN m (m * x + g) = m * x + (g + 1) % m := by
  unfold shiftN
  rw [Nat.mul_add_div hm, Nat.mul_add_mod, Nat.div_eq_of_lt hg, Nat.mod_eq_of_lt hg, add_zero]

theorem shiftN_iter {m x h : ℕ} (hm : 0 < m) (hh : h < m) (j : ℕ) :
    (shiftN m)^[j] (m * x + h) = m * x + (h + j) % m := by
  induction j with
  | zero => simp [Nat.mod_eq_of_lt hh]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, shiftN_fib hm (Nat.mod_lt _ hm), Nat.mod_add_mod,
      show h + (j + 1) = h + j + 1 by omega]

theorem shiftN_lt {m k n v : ℕ} (hm : 0 < m) (hn : n = m * k) (hv : v < n) : shiftN m v < n := by
  subst hn
  have h1 : v / m < k := by
    rw [Nat.div_lt_iff_lt_mul hm, Nat.mul_comm]
    exact hv
  have h2 : (v % m + 1) % m < m := Nat.mod_lt _ hm
  have h3 : shiftN m v < m * (v / m + 1) := by
    unfold shiftN
    rw [Nat.mul_add, mul_one]
    exact Nat.add_lt_add_left h2 _
  have h4 : m * (v / m + 1) ≤ m * k := Nat.mul_le_mul_left m (by omega)
  exact lt_of_lt_of_le h3 h4

/-- The shift on `Fin n`, for `n = m * k`. -/
def tauF {n m k : ℕ} (hm : 0 < m) (hn : n = m * k) (v : Fin n) : Fin n :=
  ⟨shiftN m v.val, shiftN_lt hm hn v.isLt⟩

theorem tauF_iter_val {n m k : ℕ} (hm : 0 < m) (hn : n = m * k) (j : ℕ) (v : Fin n) :
    ((tauF hm hn)^[j] v).val = (shiftN m)^[j] v.val := by
  induction j generalizing v with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [tauF] at ih ⊢
    rw [ih]

/-- The shift has order dividing `m`. -/
theorem tauF_pow_m {n m k : ℕ} (hm : 0 < m) (hn : n = m * k) (v : Fin n) :
    (tauF hm hn)^[m] v = v := by
  apply Fin.ext
  rw [tauF_iter_val]
  have hv := Nat.div_add_mod v.val m
  calc (shiftN m)^[m] v.val = (shiftN m)^[m] (m * (v.val / m) + v.val % m) := by rw [hv]
    _ = m * (v.val / m) + (v.val % m + m) % m := shiftN_iter hm (Nat.mod_lt _ hm) m
    _ = v.val := by
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (Nat.mod_lt _ hm), hv]

/-- The shift is injective (it has an inverse, `τ^[m-1]`). -/
theorem tauF_inj {n m k : ℕ} (hm : 0 < m) (hn : n = m * k) (x y : Fin n)
    (h : tauF hm hn x = tauF hm hn y) : x = y := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hx : (tauF hm hn)^[m'] (tauF hm hn x) = x :=
    (Function.iterate_succ_apply (tauF hm hn) m' x).symm.trans (tauF_pow_m hm hn x)
  have hy : (tauF hm hn)^[m'] (tauF hm hn y) = y :=
    (Function.iterate_succ_apply (tauF hm hn) m' y).symm.trans (tauF_pow_m hm hn y)
  calc x = (tauF hm hn)^[m'] (tauF hm hn x) := hx.symm
    _ = (tauF hm hn)^[m'] (tauF hm hn y) := by rw [h]
    _ = y := hy

/-! ## 5. The automorphism check -/

/-- The Bool check that the shift maps each neighbour list into the list of the image. -/
def homOKRange (m K : ℕ) {n : ℕ} (adj : List (List (Fin n))) (lo cnt : ℕ) : Bool :=
  (List.range' lo cnt).all fun v =>
    (Tree.get [] K (Tree.build [] K adj) v).all fun u =>
      (Tree.get [] K (Tree.build [] K adj) (shiftN m v)).any fun w => w.val == shiftN m u.val

/-- The shift check on all `n` vertices. -/
def homOK (m K : ℕ) {n : ℕ} (adj : List (List (Fin n))) : Bool :=
  homOKRange m K adj 0 n

/-- Two adjacent ranges of the shift check give their union (offsets as equations, as `checkLocalRange_join`). -/
theorem homOKRange_join {m K n : ℕ} {adj : List (List (Fin n))}
    {lo m' cnt lo2 tot : ℕ} (hl : lo + m' = lo2) (hc : m' + cnt = tot)
    (h1 : homOKRange m K adj lo m' = true) (h2 : homOKRange m K adj lo2 cnt = true) :
    homOKRange m K adj lo tot = true := by
  subst hl
  subst hc
  unfold homOKRange at h1 h2 ⊢
  rw [← List.range'_append, List.all_append]
  rw [h1, Bool.true_and]
  simpa [Nat.one_mul] using h2

theorem homOK_spec {m K n : ℕ} (hK : n ≤ 2 ^ K) (adj : List (List (Fin n)))
    (hsh : ∀ v < n, shiftN m v < n) (h : homOK m K adj = true) (v u : Fin n)
    (hu : u ∈ adj.getD v.val []) :
    ∃ w ∈ adj.getD (shiftN m v.val) [], w.val = shiftN m u.val := by
  unfold homOK homOKRange at h
  have hv := (List.all_eq_true.mp h) v.val (List.mem_range'_1.mpr ⟨Nat.zero_le _, by rw [Nat.zero_add]; exact v.isLt⟩)
  have hu' : u ∈ Tree.get [] K (Tree.build [] K adj) v.val := by
    rw [get_build_fin hK]
    exact hu
  have hany : (Tree.get [] K (Tree.build [] K adj) (shiftN m v.val)).any
      (fun w => w.val == shiftN m u.val) = true := (List.all_eq_true.mp hv) u hu'
  have hlt : shiftN m v.val < 2 ^ K := lt_of_lt_of_le (hsh v.val v.isLt) hK
  rw [get_build [] K adj (shiftN m v.val) hlt] at hany
  obtain ⟨w, hw, hwv⟩ := List.any_eq_true.mp hany
  exact ⟨w, hw, beq_iff_eq.mp hwv⟩

/-- The shift preserves adjacency of `gOf adj`, given the check. -/
theorem tauF_isHom {n m k K : ℕ} (hm : 0 < m) (hn : n = m * k) (hK : n ≤ 2 ^ K)
    (adj : List (List (Fin n))) (hhom : homOK m K adj = true) :
    IsHom (gOf adj) (tauF hm hn) := by
  have hsh : ∀ v < n, shiftN m v < n := fun v hv => shiftN_lt hm hn hv
  intro x y hxy
  simp only [gOf, graphOf, SimpleGraph.fromRel_adj] at hxy ⊢
  obtain ⟨hne, hmem⟩ := hxy
  refine ⟨fun h => hne (tauF_inj hm hn x y h), ?_⟩
  rcases hmem with h | h
  · left
    obtain ⟨w, hw, hwv⟩ := homOK_spec hK adj hsh hhom x y h
    have hwe : w = tauF hm hn y := Fin.ext hwv
    rw [hwe] at hw
    exact hw
  · right
    obtain ⟨w, hw, hwv⟩ := homOK_spec hK adj hsh hhom y x h
    have hwe : w = tauF hm hn x := Fin.ext hwv
    rw [hwe] at hw
    exact hw

/-- Every `u` lies in the orbit `τ^[j] r` of the representative `r` of its fibre. -/
theorem tauF_reach {n m k : ℕ} (hm : 0 < m) (hn : n = m * k) (u r : Fin n)
    (hr : r.val = m * (u.val / m)) : (tauF hm hn)^[u.val % m] r = u := by
  apply Fin.ext
  rw [tauF_iter_val, hr]
  have e := shiftN_iter (x := u.val / m) (h := 0) hm hm (u.val % m)
  rw [add_zero] at e
  rw [e, zero_add, Nat.mod_eq_of_lt (Nat.mod_lt _ hm)]
  exact Nat.div_add_mod u.val m

/-! ## 6. The base masks and the lift theorem -/

/-- Bit `i` of the level-0 mask at `v` is set exactly when `v = m i`. -/
theorem repLevel0_testBit {n m k : ℕ} (hm : 0 < m) (hn : n = m * k) (hpos : 0 < n) (i : ℕ)
    (v : Fin n) (h : ((repLevel0 m n).getD v.val 0).testBit i = true) :
    (⟨m * i % n, Nat.mod_lt _ hpos⟩ : Fin n) = v := by
  have hget : (repLevel0 m n).getD v.val 0 = if v.val % m = 0 then 2 ^ (v.val / m) else 0 := by
    simp [repLevel0, List.getD_eq_getElem?_getD, v.isLt]
  rw [hget] at h
  split_ifs at h with hv0
  · rw [Nat.testBit_two_pow] at h
    have hi : v.val / m = i := of_decide_eq_true h
    apply Fin.ext
    show m * i % n = v.val
    rw [← hi, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hv0), Nat.mod_eq_of_lt v.isLt]
  · simp at h

/-- **The lift theorem.** Data: the masks `L 1 … L D` (with `L 0 = repLevel0 m n` and `L D` full), and the
checks `checkLocal` (degrees, symmetry, colouring) and `homOK` (the shift preserves adjacency). Then the graph
of `adj` is bipartite, of degree at most `d`, with diameter at most `D`. Only the `k = n / m` representatives
need the ball check: their masks are `k` bits wide. -/
theorem lift_sound {n m k K d D : ℕ} (hn : n = m * k) (hm : 0 < m) (hk : 0 < k) (hK : n ≤ 2 ^ K)
    (adj : List (List (Fin n))) (col : List Bool)
    (hloc : checkLocal K d adj col = true)
    (hhom : homOK m K adj = true)
    (L : ℕ → List ℕ) (hL0 : L 0 = repLevel0 m n)
    (hs : ∀ r < D, step K (Tree.build [] K adj) (L r) = L (r + 1))
    (hfull : L D = List.replicate n (2 ^ k - 1)) :
    ∃ G : SimpleGraph (Fin n), IsBipartiteDegDiam G d D := by
  have hpos : 0 < n := by rw [hn]; exact Nat.mul_pos hm hk
  let rv : ℕ → Fin n := fun i => ⟨m * i % n, Nat.mod_lt _ hpos⟩
  have h0 : ∀ (i : ℕ) (v : Fin n), ((L 0).getD v.val 0).testBit i = true → rv i = v := by
    intro i v h
    rw [hL0] at h
    exact repLevel0_testBit hm hn hpos i v h
  have hch := edist_le_of_chain adj hK rv L h0 hs
  have hτ : IsHom (gOf adj) (tauF hm hn) := tauF_isHom hm hn hK adj hhom
  have hrep : ∀ (i : Fin k) (w : Fin n), (gOf adj).edist (rv i.val) w ≤ D := by
    intro i w
    have hval : (L D).getD w.val 0 = 2 ^ k - 1 := by
      rw [hfull]
      simp [List.getD_eq_getElem?_getD, w.isLt]
    have hbit : ((L D).getD w.val 0).testBit i.val = true := by
      rw [hval, Nat.testBit_two_pow_sub_one]
      simp [i.isLt]
    exact hch D le_rfl i.val w hbit
  have hcov : ∀ u : Fin n, ∃ i : Fin k, ∃ j < m, (tauF hm hn)^[j] (rv i.val) = u := by
    intro u
    have hu : u.val < m * k := by rw [← hn]; exact u.isLt
    have hq : u.val / m < k := (Nat.div_lt_iff_lt_mul hm).2 (by rw [Nat.mul_comm]; exact hu)
    refine ⟨⟨u.val / m, hq⟩, u.val % m, Nat.mod_lt _ hm, ?_⟩
    apply tauF_reach hm hn u
    show m * (u.val / m) % n = m * (u.val / m)
    apply Nat.mod_eq_of_lt
    exact lt_of_lt_of_eq ((Nat.mul_lt_mul_left hm).2 hq) hn.symm
  have hdiam : (gOf adj).ediam ≤ D :=
    ediam_le_of_orbits hτ (tauF_pow_m hm hn) (fun i : Fin k => rv i.val) hrep hcov
  exact ⟨gOf adj, isBipartiteDegDiam_of_local adj (fun u => col.getD u.val false) d D
    (local_spec adj col hK hloc) hdiam⟩


end BipartiteDD.Orbit
