import BipartiteDD.Fast
import BipartiteDD.LeanAll.Look
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # Orbit BFS, version 2: data as trees, loops by `Nat.rec`

Same method as `LeanAll.Orbit` (bitmask search from orbit representatives plus checked automorphisms), with two
changes that matter for the kernel on graphs with tens of thousands of vertices:

* loops over vertex ranges are `Nat.rec` directly (structural recursion through `brecOn` costs time quadratic in
  the range in the kernel);
* the graph is given by a function `nb : ℕ → List ℕ` (neighbour lists), the colouring by `c : ℕ → Bool` and the
  generators by functions `ℕ → ℕ`. Record files define them as lookups in balanced trees written out as data
  (`Tree.get`), so the kernel never converts long lists into trees.

The graph is `graphF n nb` on `Fin n`. The checks are `localOK`, `permOK`, `orbitOK`, `bfsOK`; `isBipartiteDegDiam_of`
assembles them. -/

namespace BipartiteDD.LeanAll.Orbit2

open BipartiteDD BipartiteDD.Fast

/-! ## Loops -/

/-- `allR f lo len` is `f (lo + len - 1) && … && f lo`, by `Nat.rec`. The index `lo + k` is built from the
recursor's own (literal) argument `k`, so no growing chain `lo + 1 + 1 + …` is ever formed. -/
def allR (f : ℕ → Bool) (lo len : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => f (lo + k) && ih) len

theorem allR_succ (f : ℕ → Bool) (lo len : ℕ) : allR f lo (len + 1) = (f (lo + len) && allR f lo len) := rfl

theorem allR_spec {f : ℕ → Bool} {lo len : ℕ} (h : allR f lo len = true) :
    ∀ i, lo ≤ i → i < lo + len → f i = true := by
  induction len with
  | zero => intro i h1 h2; omega
  | succ len ih =>
    intro i h1 h2
    rw [allR_succ, Bool.and_eq_true] at h
    by_cases hi : i = lo + len
    · subst hi; exact h.1
    · exact ih h.2 i h1 (by omega)

theorem allR_one (f : ℕ → Bool) (u : ℕ) : allR f u 1 = (f u && true) := by
  simp [allR_succ, allR]

/-! List loops by `List.rec` (no `brecOn`): `foldOr`, `allL`, `anyL`, `lenL`; and `bx` for `≠` on `Bool`. -/

/-- `l.foldl (fun acc u => acc ||| f u) init`. -/
def foldOr (f : ℕ → ℕ) (l : List ℕ) (init : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc) (fun u _ ih acc => ih (Nat.lor acc (f u))) l init

theorem foldOr_eq (f : ℕ → ℕ) (l : List ℕ) (init : ℕ) :
    foldOr f l init = l.foldl (fun acc u => acc ||| f u) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => exact ih _

/-- `l.all p`. -/
def allL (p : ℕ → Bool) (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun u _ ih => p u && ih) l

theorem allL_eq (p : ℕ → Bool) (l : List ℕ) : allL p l = l.all p := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.all_cons, ← ih]; rfl

/-- `l.any p`. -/
def anyL (p : ℕ → Bool) (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun u _ ih => p u || ih) l

theorem anyL_eq (p : ℕ → Bool) (l : List ℕ) : anyL p l = l.any p := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.any_cons, ← ih]; rfl

/-- `l.length`. -/
def lenL (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun _ _ ih => Nat.succ ih) l

theorem lenL_eq (l : List ℕ) : lenL l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.length_cons, ← ih]; rfl

/-- `a != b` on `Bool`. -/
def bx (a b : Bool) : Bool := cond a (cond b false true) b

theorem bx_eq (a b : Bool) : bx a b = (a != b) := by cases a <;> cases b <;> rfl

/-- The tree whose leaf `i` is `f (off + i)`, for `i < 2 ^ k`, by `Nat.rec` on the depth. -/
def Tree.gen {α : Type} (f : ℕ → α) (off k : ℕ) : Tree α :=
  Nat.rec (motive := fun _ => ℕ → Tree α) (fun off => .leaf (f off))
    (fun k ih off => .node (ih off) (ih (off + 2 ^ k))) k off

theorem Tree.gen_zero {α : Type} (f : ℕ → α) (off : ℕ) : Tree.gen f off 0 = .leaf (f off) := rfl

theorem Tree.gen_succ {α : Type} (f : ℕ → α) (off k : ℕ) :
    Tree.gen f off (k + 1) = .node (Tree.gen f off k) (Tree.gen f (off + 2 ^ k) k) := rfl

theorem look_leaf {α : Type} (x : α) (k i : ℕ) : look (.leaf x) k i = x := rfl

theorem look_node {α : Type} (l r : Tree α) (k i : ℕ) :
    look (.node l r) (k + 1) i = cond (Nat.beq (Nat.land (Nat.shiftRight i k) 1) 0) (look l k i) (look r k i) :=
  rfl

theorem mod_two_pow_succ' (i k : ℕ) :
    i % 2 ^ (k + 1) = i % 2 ^ k + (if i / 2 ^ k % 2 = 0 then 0 else 2 ^ k) := by
  rw [Nat.mod_pow_succ]
  have h2 : i / 2 ^ k % 2 = 0 ∨ i / 2 ^ k % 2 = 1 := by omega
  rcases h2 with h | h <;> simp [h]

theorem look_gen {α : Type} (f : ℕ → α) (k : ℕ) :
    ∀ off i, look (Tree.gen f off k) k i = f (off + i % 2 ^ k) := by
  induction k with
  | zero =>
    intro off i
    simp [Tree.gen_zero, look_leaf, Nat.mod_one]
  | succ k ih =>
    intro off i
    rw [Tree.gen_succ, look_node, ih, ih]
    have hb : Nat.land (Nat.shiftRight i k) 1 = i / 2 ^ k % 2 := by
      rw [← Nat.and_one_is_mod]
      show (i >>> k) &&& 1 = (i / 2 ^ k) &&& 1
      rw [Nat.shiftRight_eq_div_pow]
    rw [hb, mod_two_pow_succ']
    by_cases h : i / 2 ^ k % 2 = 0
    · have : Nat.beq (i / 2 ^ k % 2) 0 = true := by simp [h]
      rw [this]
      simp [h]
    · have : Nat.beq (i / 2 ^ k % 2) 0 = false :=
        Bool.eq_false_iff.mpr (fun h' => h (Nat.eq_of_beq_eq_true h'))
      rw [this]
      simp only [h, ↓reduceIte, Bool.cond_false]
      congr 1
      omega

theorem look_gen_lt {α : Type} (f : ℕ → α) (k : ℕ) (i : ℕ) (hi : i < 2 ^ k) :
    look (Tree.gen f 0 k) k i = f i := by
  rw [look_gen, Nat.mod_eq_of_lt hi, Nat.zero_add]

/-! ## The graph -/

variable {n : ℕ}

/-- The graph of the neighbour lists `nb`. -/
def graphF (n : ℕ) (nb : ℕ → List ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => v.val ∈ nb u.val

/-- The local check on `lo ≤ u < lo + len`: at most `d` neighbours, all `< n`, symmetric, colours differ. -/
def localOK (d n : ℕ) (nb : ℕ → List ℕ) (c : ℕ → Bool) (lo len : ℕ) : Bool :=
  allR (fun u =>
    Nat.ble (lenL (nb u)) d &&
    allL (fun v => Nat.blt v n && anyL (fun w => Nat.beq w u) (nb v) && bx (c u) (c v)) (nb u)) lo len

/-- What the local check gives, for all vertices. -/
structure LocalSpec (d n : ℕ) (nb : ℕ → List ℕ) (c : ℕ → Bool) : Prop where
  deg : ∀ u < n, (nb u).length ≤ d
  lt : ∀ u < n, ∀ v ∈ nb u, v < n
  symm : ∀ u < n, ∀ v ∈ nb u, u ∈ nb v
  col : ∀ u < n, ∀ v ∈ nb u, c u ≠ c v

theorem localSpec_of {d n : ℕ} {nb : ℕ → List ℕ} {c : ℕ → Bool}
    (h : ∀ u < n, localOK d n nb c u 1 = true) : LocalSpec d n nb c := by
  have key : ∀ u < n, (nb u).length ≤ d ∧ ∀ v ∈ nb u, v < n ∧ u ∈ nb v ∧ c u ≠ c v := by
    intro u hu
    have h1 := allR_spec (h u hu) u (le_refl u) (by omega)
    simp only [lenL_eq, allL_eq, anyL_eq, bx_eq] at h1
    simp only [Bool.and_eq_true, Nat.ble_eq, List.all_eq_true, Nat.blt_eq, List.any_eq_true,
      Nat.beq_eq, bne_iff_ne, ne_eq] at h1
    refine ⟨h1.1, fun v hv => ?_⟩
    obtain ⟨⟨hvn, w, hw, hwu⟩, hc⟩ := h1.2 v hv
    subst hwu
    exact ⟨hvn, hw, hc⟩
  exact ⟨fun u hu => (key u hu).1, fun u hu v hv => ((key u hu).2 v hv).1,
    fun u hu v hv => ((key u hu).2 v hv).2.1, fun u hu v hv => ((key u hu).2 v hv).2.2⟩

/-- A range check gives the check at every vertex of the range. -/
theorem localOK_one {d n : ℕ} {nb : ℕ → List ℕ} {c : ℕ → Bool} {lo len : ℕ}
    (h : localOK d n nb c lo len = true) : ∀ u, lo ≤ u → u < lo + len → localOK d n nb c u 1 = true := by
  intro u h1 h2
  have := allR_spec h u h1 h2
  simp only [localOK, allR_one] at this ⊢
  rw [this]
  rfl

theorem adj_iff {d : ℕ} {nb : ℕ → List ℕ} {c : ℕ → Bool} (hL : LocalSpec d n nb c)
    {u v : Fin n} : (graphF n nb).Adj u v ↔ v.val ∈ nb u.val := by
  simp only [graphF, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact hL.symm v.val v.isLt u.val h
  · intro h
    refine ⟨fun huv => ?_, Or.inl h⟩
    subst huv
    exact hL.col u.val u.isLt u.val h rfl

theorem colorable {d : ℕ} {nb : ℕ → List ℕ} {c : ℕ → Bool} (hL : LocalSpec d n nb c) :
    (graphF n nb).Colorable 2 := by
  let C : (graphF n nb).Coloring (Fin 2) :=
    SimpleGraph.Coloring.mk (fun v => if c v.val then 1 else 0) (by
      intro v w hvw
      have hw := (adj_iff hL).1 hvw
      have hc := hL.col v.val v.isLt w.val hw
      by_cases hv : c v.val <;> by_cases hw' : c w.val <;> simp_all)
  exact ⟨C⟩

theorem degree_le {d : ℕ} {nb : ℕ → List ℕ} {c : ℕ → Bool} (hL : LocalSpec d n nb c)
    (u : Fin n) : ((graphF n nb).neighborSet u).ncard ≤ d := by
  have hsub : Fin.val '' (graphF n nb).neighborSet u ⊆ ↑(nb u.val).toFinset := by
    rintro _ ⟨w, hw, rfl⟩
    rw [SimpleGraph.mem_neighborSet, adj_iff hL] at hw
    simpa using hw
  calc ((graphF n nb).neighborSet u).ncard
      = (Fin.val '' (graphF n nb).neighborSet u).ncard :=
        (Set.ncard_image_of_injective _ Fin.val_injective).symm
    _ ≤ (((nb u.val).toFinset : Finset ℕ) : Set ℕ).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (nb u.val).toFinset.card := Set.ncard_coe_finset _
    _ ≤ (nb u.val).length := List.toFinset_card_le _
    _ ≤ d := hL.deg u.val u.isLt

/-! ## Bitmask search from a block of sources -/

/-- The start masks: source `lo + j` carries bit `j`. -/
def initMask (lo k v : ℕ) : ℕ := cond (Nat.ble lo v && Nat.blt v (lo + k)) (2 ^ (v - lo)) 0

/-- One radius step on trees. -/
noncomputable def stepT (K : ℕ) (nb : ℕ → List ℕ) (cur : Tree ℕ) : Tree ℕ :=
  Tree.gen (fun v => foldOr (fun u => look cur K u) (nb v) (look cur K v)) 0 K

/-- The masks after `r` steps. -/
noncomputable def levelT (K lo k : ℕ) (nb : ℕ → List ℕ) : ℕ → Tree ℕ
  | 0 => Tree.gen (initMask lo k) 0 K
  | r + 1 => stepT K nb (levelT K lo k nb r)

/-- The search from the sources `lo … lo+k-1` fills every mask of a vertex `< n` within `D` steps. -/
noncomputable def bfsOK (K D n lo k : ℕ) (nb : ℕ → List ℕ) : Bool :=
  allR (fun v => Nat.beq (look (levelT K lo k nb D) K v) (2 ^ k - 1)) 0 n

/-- The masks, as a function. -/
def ballM (nb : ℕ → List ℕ) (lo k : ℕ) : ℕ → ℕ → ℕ
  | 0, v => initMask lo k v
  | r + 1, v => (nb v).foldl (fun acc u => acc ||| ballM nb lo k r u) (ballM nb lo k r v)

theorem foldl_or_congr (l : List ℕ) (f g : ℕ → ℕ) (h : ∀ u ∈ l, f u = g u) (init : ℕ) :
    l.foldl (fun acc u => acc ||| f u) init = l.foldl (fun acc u => acc ||| g u) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    rw [h a (by simp), ih (fun u hu => h u (by simp [hu]))]

theorem levelT_get {K lo k : ℕ} {nb : ℕ → List ℕ} {d : ℕ} {c : ℕ → Bool}
    (hL : LocalSpec d n nb c) (hK : n ≤ 2 ^ K) :
    ∀ r, ∀ v < n, look (levelT K lo k nb r) K v = ballM nb lo k r v := by
  intro r
  induction r with
  | zero =>
    intro v hv
    simp only [levelT, ballM]
    rw [look_gen_lt _ K v (by omega)]
  | succ r ih =>
    intro v hv
    simp only [levelT, stepT, ballM]
    rw [look_gen_lt _ K v (by omega), foldOr_eq, ih v hv]
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
  cases hc : (Nat.ble lo v && Nat.blt v (lo + k))
  · rw [hc] at h
    simp at h
  · rw [hc] at h
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hc
    simp only [cond_true, Nat.testBit_two_pow] at h
    have : v - lo = j := of_decide_eq_true h
    omega

theorem edist_of_testBit {nb : ℕ → List ℕ} {d : ℕ} {c : ℕ → Bool} (hL : LocalSpec d n nb c)
    (lo k : ℕ) : ∀ r, ∀ (v : Fin n) (j : ℕ), (ballM nb lo k r v.val).testBit j = true →
      ∃ hj : lo + j < n, (graphF n nb).edist v ⟨lo + j, hj⟩ ≤ r := by
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
      have hadj : (graphF n nb).Adj v ⟨u, hun⟩ := (adj_iff hL).2 hu
      calc (graphF n nb).edist v ⟨lo + j, hj⟩
          ≤ (graphF n nb).edist v ⟨u, hun⟩ + (graphF n nb).edist ⟨u, hun⟩ ⟨lo + j, hj⟩ :=
            SimpleGraph.edist_triangle
        _ ≤ 1 + r := add_le_add (SimpleGraph.edist_le_one_iff_adj_or_eq.2 (Or.inl hadj)) he
        _ = ((r + 1 : ℕ) : ℕ∞) := by push_cast; exact add_comm 1 (r : ℕ∞)

/-- A passing search: every source `lo + j` (`j < k`) is within `D` of every vertex. -/
theorem edist_of_bfs {K D lo k : ℕ} {nb : ℕ → List ℕ} {d : ℕ} {c : ℕ → Bool}
    (hL : LocalSpec d n nb c) (hK : n ≤ 2 ^ K) (h : bfsOK K D n lo k nb = true)
    (v : Fin n) (j : ℕ) (hj : j < k) (hjn : lo + j < n) :
    (graphF n nb).edist v ⟨lo + j, hjn⟩ ≤ D := by
  have hv := allR_spec h v.val (Nat.zero_le _) (by omega)
  simp only [Nat.beq_eq] at hv
  rw [levelT_get hL hK D v.val v.isLt] at hv
  have hb : (ballM nb lo k D v.val).testBit j = true := by
    rw [hv, Nat.testBit_two_pow_sub_one]
    simpa using hj
  obtain ⟨_, he⟩ := edist_of_testBit hL lo k D v j hb
  exact he

/-- The same, for a source `s` with `lo ≤ s < lo + k`. -/
theorem edist_of_bfs' {K D lo k : ℕ} {nb : ℕ → List ℕ} {d : ℕ} {c : ℕ → Bool}
    (hL : LocalSpec d n nb c) (hK : n ≤ 2 ^ K) (h : bfsOK K D n lo k nb = true)
    (v : Fin n) (s : ℕ) (hs : s < n) (h1 : lo ≤ s) (h2 : s < lo + k) :
    (graphF n nb).edist v ⟨s, hs⟩ ≤ D := by
  have := edist_of_bfs hL hK h v (s - lo) (by omega) (by omega)
  have e : (⟨lo + (s - lo), by omega⟩ : Fin n) = ⟨s, hs⟩ := Fin.ext (by simp only; omega)
  rwa [e] at this

/-! ## Staged search: the masks of each radius are data, each step is checked on its own -/

/-- The step from the masks `cur` to the masks `nxt`, checked on `lo ≤ v < lo + len`. -/
noncomputable def stepOK (K : ℕ) (nb : ℕ → List ℕ) (cur nxt : Tree ℕ) (lo len : ℕ) : Bool :=
  allR (fun v => Nat.beq (foldOr (fun u => look cur K u) (nb v) (look cur K v)) (look nxt K v)) lo len

theorem stepOK_pt {K : ℕ} {nb : ℕ → List ℕ} {cur nxt : Tree ℕ} {lo len : ℕ}
    (h : stepOK K nb cur nxt lo len = true) :
    ∀ v, lo ≤ v → v < lo + len → look nxt K v = foldOr (fun u => look cur K u) (nb v) (look cur K v) := by
  intro v h1 h2
  have := allR_spec h v h1 h2
  simp only [Nat.beq_eq] at this
  exact this.symm

/-- The full masks, as a tree. -/
noncomputable def fullT (K k : ℕ) : Tree ℕ := Tree.gen (fun _ => 2 ^ k - 1) 0 K

/-- A chain of mask trees `L 0 = start`, `L (r+1) = step (L r)` (on vertices `< n`), `L D = full`: every source
`lo + j` (`j < k`) is within `D` of every vertex. -/
theorem edist_of_staged {K D lo k : ℕ} {nb : ℕ → List ℕ} {d : ℕ} {c : ℕ → Bool}
    (hL : LocalSpec d n nb c) (hK : n ≤ 2 ^ K) (L : ℕ → Tree ℕ)
    (h0 : L 0 = Tree.gen (initMask lo k) 0 K) (hD : L D = fullT K k)
    (hs : ∀ r < D, ∀ v < n, look (L (r + 1)) K v = foldOr (fun u => look (L r) K u) (nb v) (look (L r) K v))
    (v : Fin n) (s : ℕ) (hs' : s < n) (h1 : lo ≤ s) (h2 : s < lo + k) :
    (graphF n nb).edist v ⟨s, hs'⟩ ≤ D := by
  have hlev : ∀ r ≤ D, ∀ v < n, look (L r) K v = ballM nb lo k r v := by
    intro r
    induction r with
    | zero =>
      intro _ v hv
      rw [h0, look_gen_lt _ K v (by omega)]
      rfl
    | succ r ih =>
      intro hr v hv
      rw [hs r (by omega) v hv, foldOr_eq, ih (by omega) v hv]
      simp only [ballM]
      exact foldl_or_congr _ _ _ (fun u hu => ih (by omega) u (hL.lt v hv u hu)) _
  have hv := hlev D (le_refl D) v.val v.isLt
  rw [hD, fullT, look_gen_lt _ K v.val (by omega)] at hv
  have hb : (ballM nb lo k D v.val).testBit (s - lo) = true := by
    rw [← hv, Nat.testBit_two_pow_sub_one]
    simp only [decide_eq_true_eq]
    omega
  obtain ⟨_, he⟩ := edist_of_testBit hL lo k D v (s - lo) hb
  have e : (⟨lo + (s - lo), by omega⟩ : Fin n) = ⟨s, hs'⟩ := Fin.ext (by simp only; omega)
  rwa [e] at he

/-! ## Automorphisms -/

/-- `σ` (with inverse `τ`) maps `0 … n-1` into itself, `τ ∘ σ = id`, and `nb (σ v) ⊆ σ (nb v)`;
checked on `lo ≤ v < lo + len`. -/
def permOK (n : ℕ) (nb : ℕ → List ℕ) (σ τ : ℕ → ℕ) (lo len : ℕ) : Bool :=
  allR (fun v =>
    Nat.blt (σ v) n && Nat.beq (τ (σ v)) v &&
    allL (fun x => anyL (fun u => Nat.beq (σ u) x) (nb v)) (nb (σ v))) lo len

/-- What a passing `permOK` gives. -/
structure PermSpec (n : ℕ) (nb : ℕ → List ℕ) (σ τ : ℕ → ℕ) : Prop where
  lt : ∀ v < n, σ v < n
  inv : ∀ v < n, τ (σ v) = v
  onto : ∀ v < n, ∀ x ∈ nb (σ v), ∃ u ∈ nb v, σ u = x

theorem permSpec_of {n : ℕ} {nb : ℕ → List ℕ} {σ τ : ℕ → ℕ}
    (h : ∀ v < n, permOK n nb σ τ v 1 = true) : PermSpec n nb σ τ := by
  have key : ∀ v < n, σ v < n ∧ τ (σ v) = v ∧ ∀ x ∈ nb (σ v), ∃ u ∈ nb v, σ u = x := by
    intro v hv
    have h1 := allR_spec (h v hv) v (le_refl v) (by omega)
    simp only [allL_eq, anyL_eq] at h1
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, List.all_eq_true, List.any_eq_true] at h1
    exact ⟨h1.1.1, h1.1.2, h1.2⟩
  exact ⟨fun v hv => (key v hv).1, fun v hv => (key v hv).2.1, fun v hv => (key v hv).2.2⟩

theorem permOK_one {n : ℕ} {nb : ℕ → List ℕ} {σ τ : ℕ → ℕ} {lo len : ℕ}
    (h : permOK n nb σ τ lo len = true) : ∀ v, lo ≤ v → v < lo + len → permOK n nb σ τ v 1 = true := by
  intro v h1 h2
  have := allR_spec h v h1 h2
  simp only [permOK, allR_one] at this ⊢
  rw [this]
  rfl

/-- The map `σ` on `Fin n`. -/
def permF {nb : ℕ → List ℕ} {σ τ : ℕ → ℕ} (hP : PermSpec n nb σ τ) (v : Fin n) : Fin n :=
  ⟨σ v.val, hP.lt v.val v.isLt⟩

theorem permF_inj {nb : ℕ → List ℕ} {σ τ : ℕ → ℕ} (hP : PermSpec n nb σ τ) {u w : Fin n}
    (h : permF hP u = permF hP w) : u = w := by
  apply Fin.ext
  have h' : σ u.val = σ w.val := congrArg Fin.val h
  rw [← hP.inv u.val u.isLt, ← hP.inv w.val w.isLt, h']

theorem walk_pull {d : ℕ} {nb : ℕ → List ℕ} {c : ℕ → Bool} (hL : LocalSpec d n nb c)
    {σ τ : ℕ → ℕ} (hP : PermSpec n nb σ τ) {a b : Fin n} (p : (graphF n nb).Walk a b) :
    ∀ u w : Fin n, permF hP u = a → permF hP w = b →
      ∃ q : (graphF n nb).Walk u w, q.length = p.length := by
  induction p with
  | nil =>
    intro u w hu hw
    have : u = w := permF_inj hP (hu.trans hw.symm)
    subst this
    exact ⟨.nil, rfl⟩
  | @cons a c' b hac p ih =>
    intro u w hu hw
    have hc : c'.val ∈ nb (σ u.val) := by
      have := (adj_iff hL).1 hac
      rw [← hu] at this
      exact this
    obtain ⟨v, hv, hvc⟩ := hP.onto u.val u.isLt c'.val hc
    have hvn : v < n := hL.lt u.val u.isLt v hv
    have hv' : permF hP ⟨v, hvn⟩ = c' := Fin.ext hvc
    obtain ⟨q, hq⟩ := ih ⟨v, hvn⟩ w hv' hw
    exact ⟨.cons ((adj_iff hL).2 hv) q, by simp [hq]⟩

theorem edist_le_perm {d : ℕ} {nb : ℕ → List ℕ} {c : ℕ → Bool} (hL : LocalSpec d n nb c)
    {σ τ : ℕ → ℕ} (hP : PermSpec n nb σ τ) (u w : Fin n) :
    (graphF n nb).edist u w ≤ (graphF n nb).edist (permF hP u) (permF hP w) := by
  by_cases hr : (graphF n nb).Reachable (permF hP u) (permF hP w)
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
    obtain ⟨q, hq⟩ := walk_pull hL hP p u w rfl rfl
    rw [← hp, ← hq]
    exact SimpleGraph.edist_le q
  · rw [SimpleGraph.edist_eq_top_of_not_reachable hr]
    exact le_top

/-- Every vertex `lo ≤ v < lo + len` has a generator moving it below `v`. Generators are pairs `(σ, σ⁻¹)`. -/
def orbitOK (gens : List ((ℕ → ℕ) × (ℕ → ℕ))) (lo len : ℕ) : Bool :=
  allR (fun v => gens.any (fun g => Nat.blt (g.1 v) v)) lo len

theorem orbit_of {gens : List ((ℕ → ℕ) × (ℕ → ℕ))} {lo len : ℕ} (h : orbitOK gens lo len = true) :
    ∀ v, lo ≤ v → v < lo + len → ∃ g ∈ gens, g.1 v < v := by
  intro v h1 h2
  have h3 := allR_spec h v h1 h2
  simp only [List.any_eq_true, Nat.blt_eq] at h3
  exact h3

/-- **Assembly.** -/
theorem ediam_le {d D m : ℕ} {nb : ℕ → List ℕ} {c : ℕ → Bool} (hL : LocalSpec d n nb c)
    (gens : List ((ℕ → ℕ) × (ℕ → ℕ)))
    (hP : ∀ g ∈ gens, PermSpec n nb g.1 g.2)
    (hO : ∀ v, m ≤ v → v < n → ∃ g ∈ gens, g.1 v < v)
    (hB : ∀ s (hs : s < n), s < m → ∀ v : Fin n, (graphF n nb).edist v ⟨s, hs⟩ ≤ D) :
    (graphF n nb).ediam ≤ D := by
  suffices h : ∀ i, ∀ v : Fin n, v.val = i → ∀ w, (graphF n nb).edist v w ≤ D by
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
      calc (graphF n nb).edist v w ≤ (graphF n nb).edist (permF hPσ v) (permF hPσ w) :=
            edist_le_perm hL hPσ v w
        _ ≤ D := ih (g.1 i) hlt (permF hPσ v) (by simp [permF, hvi]) (permF hPσ w)

/-- The record form. -/
theorem isBipartiteDegDiam_of {d D m : ℕ} {nb : ℕ → List ℕ} {c : ℕ → Bool}
    (hL : LocalSpec d n nb c) (gens : List ((ℕ → ℕ) × (ℕ → ℕ)))
    (hP : ∀ g ∈ gens, PermSpec n nb g.1 g.2)
    (hO : ∀ v, m ≤ v → v < n → ∃ g ∈ gens, g.1 v < v)
    (hB : ∀ s (hs : s < n), s < m → ∀ v : Fin n, (graphF n nb).edist v ⟨s, hs⟩ ≤ D) :
    IsBipartiteDegDiam (graphF n nb) d D :=
  ⟨colorable hL, degree_le hL, ediam_le hL gens hP hO hB⟩

end BipartiteDD.LeanAll.Orbit2
