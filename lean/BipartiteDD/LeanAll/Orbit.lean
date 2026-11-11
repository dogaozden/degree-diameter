import BipartiteDD.Fast

/-! # Orbit BFS: diameter from a few sources and verified automorphisms

A graph on `Fin n` is given by neighbour lists `adj : List (List ℕ)` (entries are vertex numbers). The checks, all
`Bool` computations on `Nat` literals meant for `decide +kernel`, are:

* `localOK`: every list has at most `d` entries, all `< n`, the lists are symmetric and a colouring `col`
  separates neighbours;
* `permOK`: a list `σ` is a permutation with inverse `τ` that maps neighbours onto neighbours
  (`adj (σ v) ⊆ σ (adj v)`), so it does not shrink distances;
* `orbitOK`: every vertex `v ≥ m` has a generator `σ` with `σ v < v` (vertices are numbered by a search from the
  representatives `0 … m-1`);
* `bfsOK`: a bitmask search from the sources `lo … lo+k-1` (one bit per source) fills every mask within `D` steps.

`ediam_le` assembles them: every representative is within `D` of everything, and every other vertex is moved to a
smaller one by a distance-preserving map. `isBipartiteDegDiam_of` gives the record form. -/

namespace BipartiteDD.LeanAll.Orbit

open BipartiteDD BipartiteDD.Fast

/-! ## Loops and trees -/

/-- `allFrom f lo len` is `f lo && … && f (lo + len - 1)`. -/
def allFrom (f : ℕ → Bool) : ℕ → ℕ → Bool
  | _, 0 => true
  | lo, len + 1 => f lo && allFrom f (lo + 1) len

theorem allFrom_spec {f : ℕ → Bool} {lo len : ℕ} (h : allFrom f lo len = true) :
    ∀ i, lo ≤ i → i < lo + len → f i = true := by
  induction len generalizing lo with
  | zero => intro i h1 h2; omega
  | succ len ih =>
    intro i h1 h2
    simp only [allFrom, Bool.and_eq_true] at h
    by_cases hi : i = lo
    · subst hi; exact h.1
    · exact ih h.2 i (by omega) (by omega)

/-- The tree whose leaf `i` is `f (off + i)`, for `i < 2 ^ k`. -/
def Tree.gen {α : Type} (f : ℕ → α) : ℕ → ℕ → Tree α
  | off, 0 => .leaf (f off)
  | off, k + 1 => .node (Tree.gen f off k) (Tree.gen f (off + 2 ^ k) k)

theorem get_gen {α : Type} (d : α) (f : ℕ → α) (k : ℕ) :
    ∀ off i, i < 2 ^ k → Tree.get d k (Tree.gen f off k) i = f (off + i) := by
  induction k with
  | zero =>
    intro off i hi
    have : i = 0 := by simp at hi; omega
    subst this
    simp [Tree.gen, Tree.get]
  | succ k ih =>
    intro off i hi
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
    simp only [Tree.gen, Tree.get]
    by_cases h : i < 2 ^ k
    · simp only [h, ↓reduceIte]
      exact ih off i h
    · simp only [h, ↓reduceIte]
      rw [ih _ _ (by omega)]
      congr 1
      omega

/-! ## The graph -/

variable {n : ℕ}

/-- The graph of the neighbour lists. -/
def graphL (n : ℕ) (adj : List (List ℕ)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => v.val ∈ adj.getD u.val []

/-- The local check on `lo ≤ u < lo + len`. -/
def localOK (K d n : ℕ) (adjT : Tree (List ℕ)) (colT : Tree Bool) (lo len : ℕ) : Bool :=
  allFrom (fun u =>
    Nat.ble (Tree.get [] K adjT u).length d &&
    (Tree.get [] K adjT u).all (fun v =>
      Nat.blt v n &&
      (Tree.get [] K adjT v).any (fun w => Nat.beq w u) &&
      (Tree.get false K colT u != Tree.get false K colT v))) lo len

/-- What the local check gives, for all vertices. -/
structure LocalSpec (d n : ℕ) (adj : List (List ℕ)) (col : List Bool) : Prop where
  deg : ∀ u < n, (adj.getD u []).length ≤ d
  lt : ∀ u < n, ∀ v ∈ adj.getD u [], v < n
  symm : ∀ u < n, ∀ v ∈ adj.getD u [], u ∈ adj.getD v []
  col : ∀ u < n, ∀ v ∈ adj.getD u [], col.getD u false ≠ col.getD v false

theorem localSpec_of {K d n : ℕ} {adj : List (List ℕ)} {col : List Bool} (hK : n ≤ 2 ^ K)
    (h : localOK K d n (Tree.build [] K adj) (Tree.build false K col) 0 n = true) :
    LocalSpec d n adj col := by
  have hA : ∀ u < n, Tree.get [] K (Tree.build [] K adj) u = adj.getD u [] :=
    fun u hu => get_build [] K adj u (by omega)
  have hC : ∀ u < n, Tree.get false K (Tree.build false K col) u = col.getD u false :=
    fun u hu => get_build false K col u (by omega)
  have hu : ∀ u < n, _ := fun u hu => allFrom_spec h u (Nat.zero_le u) (by omega)
  have key : ∀ u < n, (adj.getD u []).length ≤ d ∧ ∀ v ∈ adj.getD u [],
      v < n ∧ u ∈ adj.getD v [] ∧ col.getD u false ≠ col.getD v false := by
    intro u hu'
    have h1 := hu u hu'
    simp only [Bool.and_eq_true, Nat.ble_eq, List.all_eq_true, Nat.blt_eq, List.any_eq_true,
      Nat.beq_eq, bne_iff_ne, ne_eq] at h1
    rw [hA u hu'] at h1
    refine ⟨h1.1, fun v hv => ?_⟩
    obtain ⟨⟨hvn, w, hw, hwu⟩, hc⟩ := h1.2 v hv
    rw [hA v hvn] at hw
    rw [hC u hu', hC v hvn] at hc
    subst hwu
    exact ⟨hvn, hw, hc⟩
  exact ⟨fun u hu => (key u hu).1, fun u hu v hv => ((key u hu).2 v hv).1,
    fun u hu v hv => ((key u hu).2 v hv).2.1, fun u hu v hv => ((key u hu).2 v hv).2.2⟩

theorem adj_iff {d : ℕ} {adj : List (List ℕ)} {col : List Bool} (hL : LocalSpec d n adj col)
    {u v : Fin n} : (graphL n adj).Adj u v ↔ v.val ∈ adj.getD u.val [] := by
  simp only [graphL, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact hL.symm v.val v.isLt u.val h
  · intro h
    refine ⟨fun huv => ?_, Or.inl h⟩
    subst huv
    exact hL.col u.val u.isLt u.val h rfl

/-! ## Bipartite and degree -/

theorem colorable {d : ℕ} {adj : List (List ℕ)} {col : List Bool} (hL : LocalSpec d n adj col) :
    (graphL n adj).Colorable 2 := by
  let C : (graphL n adj).Coloring (Fin 2) :=
    SimpleGraph.Coloring.mk (fun v => if col.getD v.val false then 1 else 0) (by
      intro v w hvw
      have hw := (adj_iff hL).1 hvw
      have hc := hL.col v.val v.isLt w.val hw
      by_cases hv : col.getD v.val false <;> by_cases hw' : col.getD w.val false <;> simp_all)
  exact ⟨C⟩

theorem degree_le {d : ℕ} {adj : List (List ℕ)} {col : List Bool} (hL : LocalSpec d n adj col)
    (u : Fin n) : ((graphL n adj).neighborSet u).ncard ≤ d := by
  have hsub : Fin.val '' (graphL n adj).neighborSet u ⊆ ↑(adj.getD u.val []).toFinset := by
    rintro _ ⟨w, hw, rfl⟩
    rw [SimpleGraph.mem_neighborSet, adj_iff hL] at hw
    simpa using hw
  calc ((graphL n adj).neighborSet u).ncard
      = (Fin.val '' (graphL n adj).neighborSet u).ncard :=
        (Set.ncard_image_of_injective _ Fin.val_injective).symm
    _ ≤ (((adj.getD u.val []).toFinset : Finset ℕ) : Set ℕ).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (adj.getD u.val []).toFinset.card := Set.ncard_coe_finset _
    _ ≤ (adj.getD u.val []).length := List.toFinset_card_le _
    _ ≤ d := hL.deg u.val u.isLt

/-! ## Bitmask search from a block of sources -/

/-- The start masks: source `lo + j` carries bit `j`. -/
def initMask (lo k v : ℕ) : ℕ := if Nat.ble lo v && Nat.blt v (lo + k) then 2 ^ (v - lo) else 0

/-- One radius step on trees: the new mask of `v` is the OR of the masks of `v` and its neighbours. -/
def stepT (K : ℕ) (adjT : Tree (List ℕ)) (cur : Tree ℕ) : Tree ℕ :=
  Tree.gen (fun v => (Tree.get [] K adjT v).foldl (fun acc u => acc ||| Tree.get 0 K cur u)
    (Tree.get 0 K cur v)) 0 K

/-- The masks after `r` steps. -/
def levelT (K lo k : ℕ) (adjT : Tree (List ℕ)) : ℕ → Tree ℕ
  | 0 => Tree.gen (initMask lo k) 0 K
  | r + 1 => stepT K adjT (levelT K lo k adjT r)

/-- The search from the sources `lo … lo+k-1` fills every mask of a vertex `< n` within `D` steps. -/
def bfsOK (K D n lo k : ℕ) (adjT : Tree (List ℕ)) : Bool :=
  let T := levelT K lo k adjT D
  allFrom (fun v => Nat.beq (Tree.get 0 K T v) (2 ^ k - 1)) 0 n

/-- The masks, as a function. -/
def ballM (adj : List (List ℕ)) (lo k : ℕ) : ℕ → ℕ → ℕ
  | 0, v => initMask lo k v
  | r + 1, v => (adj.getD v []).foldl (fun acc u => acc ||| ballM adj lo k r u) (ballM adj lo k r v)

theorem foldl_or_congr (l : List ℕ) (f g : ℕ → ℕ) (h : ∀ u ∈ l, f u = g u) (init : ℕ) :
    l.foldl (fun acc u => acc ||| f u) init = l.foldl (fun acc u => acc ||| g u) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    rw [h a (by simp), ih (fun u hu => h u (by simp [hu]))]

theorem levelT_get {K lo k : ℕ} {adj : List (List ℕ)} {d : ℕ} {col : List Bool}
    (hL : LocalSpec d n adj col) (hK : n ≤ 2 ^ K) :
    ∀ r, ∀ v < n, Tree.get 0 K (levelT K lo k (Tree.build [] K adj) r) v = ballM adj lo k r v := by
  intro r
  induction r with
  | zero =>
    intro v hv
    simp only [levelT, ballM]
    rw [get_gen 0 _ K 0 v (by omega), Nat.zero_add]
  | succ r ih =>
    intro v hv
    simp only [levelT, stepT, ballM]
    rw [get_gen 0 _ K 0 v (by omega), Nat.zero_add, get_build [] K adj v (by omega), ih v hv]
    exact foldl_or_congr _ _ _ (fun u hu => ih u (hL.lt v hv u hu)) _

theorem testBit_foldl_or' (l : List ℕ) (f : ℕ → ℕ) (init w : ℕ) :
    (l.foldl (fun acc u => acc ||| f u) init).testBit w = true ↔
      init.testBit w = true ∨ ∃ u ∈ l, (f u).testBit w = true := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, List.mem_cons, exists_eq_or_imp, Bool.or_eq_true]
    tauto

theorem testBit_initMask {lo k v j : ℕ} (h : (initMask lo k v).testBit j = true) :
    v = lo + j ∧ j < k := by
  unfold initMask at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hc
    rw [Nat.testBit_two_pow] at h
    have : v - lo = j := of_decide_eq_true h
    omega
  · simp at h

/-- A bit `j` in the mask of `v` after `r` steps means the source `lo + j` is within `r` of `v`. -/
theorem edist_of_testBit {adj : List (List ℕ)} {d : ℕ} {col : List Bool} (hL : LocalSpec d n adj col)
    (lo k : ℕ) : ∀ r, ∀ (v : Fin n) (j : ℕ), (ballM adj lo k r v.val).testBit j = true →
      ∃ hj : lo + j < n, (graphL n adj).edist v ⟨lo + j, hj⟩ ≤ r := by
  intro r
  induction r with
  | zero =>
    intro v j h
    obtain ⟨hv, -⟩ := testBit_initMask h
    refine ⟨hv ▸ v.isLt, ?_⟩
    have : v = ⟨lo + j, hv ▸ v.isLt⟩ := Fin.ext hv
    rw [← this, SimpleGraph.edist_self]
    exact le_refl _
  | succ r ih =>
    intro v j h
    simp only [ballM, testBit_foldl_or'] at h
    rcases h with h | ⟨u, hu, hb⟩
    · obtain ⟨hj, he⟩ := ih v j h
      exact ⟨hj, he.trans (by exact_mod_cast Nat.le_succ r)⟩
    · have hun : u < n := hL.lt v.val v.isLt u hu
      obtain ⟨hj, he⟩ := ih ⟨u, hun⟩ j hb
      refine ⟨hj, ?_⟩
      have hadj : (graphL n adj).Adj v ⟨u, hun⟩ := (adj_iff hL).2 hu
      calc (graphL n adj).edist v ⟨lo + j, hj⟩
          ≤ (graphL n adj).edist v ⟨u, hun⟩ + (graphL n adj).edist ⟨u, hun⟩ ⟨lo + j, hj⟩ :=
            SimpleGraph.edist_triangle
        _ ≤ 1 + r := add_le_add (SimpleGraph.edist_le_one_iff_adj_or_eq.2 (Or.inl hadj)) he
        _ = ((r + 1 : ℕ) : ℕ∞) := by push_cast; exact add_comm 1 (r : ℕ∞)

/-- A passing search: every source `lo + j` (`j < k`) is within `D` of every vertex. -/
theorem edist_of_bfs {K D lo k : ℕ} {adj : List (List ℕ)} {d : ℕ} {col : List Bool}
    (hL : LocalSpec d n adj col) (hK : n ≤ 2 ^ K) (h : bfsOK K D n lo k (Tree.build [] K adj) = true)
    (v : Fin n) (j : ℕ) (hj : j < k) (hjn : lo + j < n) :
    (graphL n adj).edist v ⟨lo + j, hjn⟩ ≤ D := by
  have hv := allFrom_spec h v.val (Nat.zero_le _) (by omega)
  simp only [Nat.beq_eq] at hv
  rw [levelT_get hL hK D v.val v.isLt] at hv
  have hb : (ballM adj lo k D v.val).testBit j = true := by
    rw [hv, Nat.testBit_two_pow_sub_one]
    simpa using hj
  obtain ⟨_, he⟩ := edist_of_testBit hL lo k D v j hb
  exact he

/-! ## Automorphisms -/

/-- `σ` (with inverse `τ`) is a bijection of `0 … n-1` that maps the neighbours of `v` onto those of `σ v`
(`adj (σ v) ⊆ σ (adj v)`), checked on `lo ≤ v < lo + len`. -/
def permOK (K n : ℕ) (adjT : Tree (List ℕ)) (σT τT : Tree ℕ) (lo len : ℕ) : Bool :=
  allFrom (fun v =>
    Nat.blt (Tree.get 0 K σT v) n &&
    Nat.beq (Tree.get 0 K τT (Tree.get 0 K σT v)) v &&
    (Tree.get [] K adjT (Tree.get 0 K σT v)).all (fun x =>
      (Tree.get [] K adjT v).any (fun u => Nat.beq (Tree.get 0 K σT u) x))) lo len

/-- What a passing `permOK` gives. -/
structure PermSpec (n : ℕ) (adj : List (List ℕ)) (σ τ : ℕ → ℕ) : Prop where
  lt : ∀ v < n, σ v < n
  inv : ∀ v < n, τ (σ v) = v
  onto : ∀ v < n, ∀ x ∈ adj.getD (σ v) [], ∃ u ∈ adj.getD v [], σ u = x

theorem permSpec_of {K n d : ℕ} {adj : List (List ℕ)} {col : List Bool} {σl τl : List ℕ}
    (hL : LocalSpec d n adj col) (hK : n ≤ 2 ^ K)
    (h : permOK K n (Tree.build [] K adj) (Tree.build 0 K σl) (Tree.build 0 K τl) 0 n = true) :
    PermSpec n adj (fun v => σl.getD v 0) (fun v => τl.getD v 0) := by
  have hA : ∀ u < n, Tree.get [] K (Tree.build [] K adj) u = adj.getD u [] :=
    fun u hu => get_build [] K adj u (by omega)
  have hS : ∀ u < n, Tree.get 0 K (Tree.build 0 K σl) u = σl.getD u 0 :=
    fun u hu => get_build 0 K σl u (by omega)
  have hT : ∀ u < n, Tree.get 0 K (Tree.build 0 K τl) u = τl.getD u 0 :=
    fun u hu => get_build 0 K τl u (by omega)
  have key : ∀ v < n, σl.getD v 0 < n ∧ τl.getD (σl.getD v 0) 0 = v ∧
      ∀ x ∈ adj.getD (σl.getD v 0) [], ∃ u ∈ adj.getD v [], σl.getD u 0 = x := by
    intro v hv
    have h1 := allFrom_spec h v (Nat.zero_le v) (by omega)
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, List.all_eq_true, List.any_eq_true] at h1
    rw [hS v hv] at h1
    obtain ⟨⟨hlt, hinv⟩, hon⟩ := h1
    rw [hT _ hlt] at hinv
    rw [hA _ hlt, hA v hv] at hon
    refine ⟨hlt, hinv, fun x hx => ?_⟩
    obtain ⟨u, hu, hux⟩ := hon x hx
    have hun : u < n := hL.lt v hv u hu
    rw [hS u hun] at hux
    exact ⟨u, hu, hux⟩
  exact ⟨fun v hv => (key v hv).1, fun v hv => (key v hv).2.1, fun v hv => (key v hv).2.2⟩

/-- The map `σ` on `Fin n`. -/
def permF {adj : List (List ℕ)} {σ τ : ℕ → ℕ} (hP : PermSpec n adj σ τ) (v : Fin n) : Fin n :=
  ⟨σ v.val, hP.lt v.val v.isLt⟩

theorem permF_inj {adj : List (List ℕ)} {σ τ : ℕ → ℕ} (hP : PermSpec n adj σ τ) {u w : Fin n}
    (h : permF hP u = permF hP w) : u = w := by
  apply Fin.ext
  have h' : σ u.val = σ w.val := congrArg Fin.val h
  rw [← hP.inv u.val u.isLt, ← hP.inv w.val w.isLt, h']

/-- A walk between images pulls back to a walk of the same length. -/
theorem walk_pull {d : ℕ} {adj : List (List ℕ)} {col : List Bool} (hL : LocalSpec d n adj col)
    {σ τ : ℕ → ℕ} (hP : PermSpec n adj σ τ) {a b : Fin n} (p : (graphL n adj).Walk a b) :
    ∀ u w : Fin n, permF hP u = a → permF hP w = b →
      ∃ q : (graphL n adj).Walk u w, q.length = p.length := by
  induction p with
  | nil =>
    intro u w hu hw
    have : u = w := permF_inj hP (hu.trans hw.symm)
    subst this
    exact ⟨.nil, rfl⟩
  | @cons a c b hac p ih =>
    intro u w hu hw
    have hc : c.val ∈ adj.getD (σ u.val) [] := by
      have := (adj_iff hL).1 hac
      rw [← hu] at this
      exact this
    obtain ⟨v, hv, hvc⟩ := hP.onto u.val u.isLt c.val hc
    have hvn : v < n := hL.lt u.val u.isLt v hv
    have hv' : permF hP ⟨v, hvn⟩ = c := Fin.ext hvc
    obtain ⟨q, hq⟩ := ih ⟨v, hvn⟩ w hv' hw
    exact ⟨.cons ((adj_iff hL).2 hv) q, by simp [hq]⟩

/-- The map `σ` does not shrink distances. -/
theorem edist_le_perm {d : ℕ} {adj : List (List ℕ)} {col : List Bool} (hL : LocalSpec d n adj col)
    {σ τ : ℕ → ℕ} (hP : PermSpec n adj σ τ) (u w : Fin n) :
    (graphL n adj).edist u w ≤ (graphL n adj).edist (permF hP u) (permF hP w) := by
  by_cases hr : (graphL n adj).Reachable (permF hP u) (permF hP w)
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
    obtain ⟨q, hq⟩ := walk_pull hL hP p u w rfl rfl
    rw [← hp, ← hq]
    exact SimpleGraph.edist_le q
  · rw [SimpleGraph.edist_eq_top_of_not_reachable hr]
    exact le_top

/-- Every vertex `v ≥ m` has a generator moving it below `v`. Generators come as pairs `(σ, σ⁻¹)`. -/
def orbitOK (K m n : ℕ) (gens : List (List ℕ × List ℕ)) : Bool :=
  let Ts := gens.map (fun g => Tree.build 0 K g.1)
  allFrom (fun v => Ts.any (fun T => Nat.blt (Tree.get 0 K T v) v)) m (n - m)

theorem orbit_of {K m n : ℕ} {gens : List (List ℕ × List ℕ)} (hK : n ≤ 2 ^ K)
    (h : orbitOK K m n gens = true) : ∀ v, m ≤ v → v < n → ∃ g ∈ gens, g.1.getD v 0 < v := by
  intro v hm hv
  have h1 := allFrom_spec h v hm (by omega)
  simp only [List.any_map, List.any_eq_true, Function.comp, Nat.blt_eq] at h1
  obtain ⟨g, hg, hlt⟩ := h1
  exact ⟨g, hg, by rwa [get_build 0 K g.1 v (by omega)] at hlt⟩

/-- **Assembly.** The representatives `0 … m-1` are within `D` of every vertex, every other vertex is moved
below itself by a distance-preserving map: then every two vertices are within `D`. -/
theorem ediam_le {d D m : ℕ} {adj : List (List ℕ)} {col : List Bool} (hL : LocalSpec d n adj col)
    (gens : List (List ℕ × List ℕ))
    (hP : ∀ g ∈ gens, PermSpec n adj (fun v => g.1.getD v 0) (fun v => g.2.getD v 0))
    (hO : ∀ v, m ≤ v → v < n → ∃ g ∈ gens, g.1.getD v 0 < v)
    (hB : ∀ s (hs : s < n), s < m → ∀ v : Fin n, (graphL n adj).edist v ⟨s, hs⟩ ≤ D) :
    (graphL n adj).ediam ≤ D := by
  suffices h : ∀ i, ∀ v : Fin n, v.val = i → ∀ w, (graphL n adj).edist v w ≤ D by
    rw [SimpleGraph.ediam_le_iff]
    exact fun v w => h v.val v rfl w
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro v hvi w
    by_cases hm : i < m
    · have hv : v = ⟨i, hvi ▸ v.isLt⟩ := Fin.ext hvi
      rw [SimpleGraph.edist_comm, hv]
      exact hB i _ hm w
    · obtain ⟨g, hg, hlt⟩ := hO i (by omega) (hvi ▸ v.isLt)
      have hPσ := hP g hg
      calc (graphL n adj).edist v w ≤ (graphL n adj).edist (permF hPσ v) (permF hPσ w) :=
            edist_le_perm hL hPσ v w
        _ ≤ D := ih (g.1.getD i 0) hlt (permF hPσ v) (by simp [permF, hvi]) (permF hPσ w)

/-- The record form. -/
theorem isBipartiteDegDiam_of {d D m : ℕ} {adj : List (List ℕ)} {col : List Bool}
    (hL : LocalSpec d n adj col) (gens : List (List ℕ × List ℕ))
    (hP : ∀ g ∈ gens, PermSpec n adj (fun v => g.1.getD v 0) (fun v => g.2.getD v 0))
    (hO : ∀ v, m ≤ v → v < n → ∃ g ∈ gens, g.1.getD v 0 < v)
    (hB : ∀ s (hs : s < n), s < m → ∀ v : Fin n, (graphL n adj).edist v ⟨s, hs⟩ ≤ D) :
    IsBipartiteDegDiam (graphL n adj) d D :=
  ⟨colorable hL, degree_le hL, ediam_le hL gens hP hO hB⟩

end BipartiteDD.LeanAll.Orbit
