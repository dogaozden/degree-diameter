import BipartiteDD.Basic

/-! A kernel-friendly version of `check`.

`ball` as defined in `Basic` recomputes every sub-call, so its cost is exponential in the radius and
the kernel cannot evaluate it. Here the balls are computed one radius at a time. Each level is kept
in a balanced binary tree, so a lookup costs `K` steps (with `2 ^ K ≥ n`). Everything is structural
recursion, and the arithmetic is on `Nat` literals, which the kernel accelerates with GMP.

`checkFast` is proved to imply `check` (`check_of_fast`), so the records can be cited through
`check_sound` as before. -/

namespace BipartiteDD.Fast

/-- A complete binary tree; the leaves hold the values. -/
inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

/-- `build d k xs` is a depth-`k` tree whose `i`-th leaf is `xs.getD i d`, for `i < 2 ^ k`. -/
def Tree.build {α : Type} (d : α) : ℕ → List α → Tree α
  | 0, xs => .leaf (xs.getD 0 d)
  | k + 1, xs => .node (Tree.build d k (xs.take (2 ^ k))) (Tree.build d k (xs.drop (2 ^ k)))

/-- Leaf `i` of a depth-`k` tree; `d` is returned on a shape mismatch, which never happens for trees
made by `build`. -/
def Tree.get {α : Type} (d : α) : ℕ → Tree α → ℕ → α
  | 0, .leaf x, _ => x
  | k + 1, .node l r, i => if i < 2 ^ k then Tree.get d k l i else Tree.get d k r (i - 2 ^ k)
  | _, _, _ => d

theorem getD_take_of_lt {α : Type} (xs : List α) (m i : ℕ) (d : α) (h : i < m) :
    (xs.take m).getD i d = xs.getD i d := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_drop_add {α : Type} (xs : List α) (m i : ℕ) (d : α) :
    (xs.drop m).getD i d = xs.getD (m + i) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem get_build {α : Type} (d : α) (k : ℕ) :
    ∀ (xs : List α) (i : ℕ), i < 2 ^ k → Tree.get d k (Tree.build d k xs) i = xs.getD i d := by
  induction k with
  | zero =>
    intro xs i hi
    have hi0 : i = 0 := by
      simp at hi
      omega
    subst hi0
    simp [Tree.build, Tree.get]
  | succ k ih =>
    intro xs i hi
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
    simp only [Tree.build, Tree.get]
    by_cases h : i < 2 ^ k
    · simp only [h, ↓reduceIte]
      rw [ih _ _ h, getD_take_of_lt _ _ _ _ h]
    · simp only [h, ↓reduceIte]
      rw [ih _ _ (by omega), getD_drop_add]
      congr 1
      omega

/-- Level 0: the mask of each vertex alone. -/
def level0 (n : ℕ) : List ℕ := (List.range n).map fun v => 2 ^ v

/-- One radius up: the masks `ball (r+1) v` for all `v`, from the masks `cur` of radius `r`.
`adjT` is the tree of neighbour lists, `K` the depth of both trees. -/
def step {n : ℕ} (K : ℕ) (adjT : Tree (List (Fin n))) (cur : List ℕ) : List ℕ :=
  let T := Tree.build 0 K cur
  (List.range n).map fun v =>
    (Tree.get [] K adjT v).foldl (fun acc u => acc ||| Tree.get 0 K T u.val) (Tree.get 0 K T v)

/-- The masks of every vertex at radius `r`. -/
def levelOf {n : ℕ} (K : ℕ) (adjT : Tree (List (Fin n))) : ℕ → List ℕ
  | 0 => level0 n
  | r + 1 => step K adjT (levelOf K adjT r)

/-- The whole check, on lists. Lookups go through trees; the ball test is `ball nbrs D u = 2 ^ n - 1`
for every `u`. -/
def checkFast (K d D : ℕ) {n : ℕ} (adj : List (List (Fin n))) (col : List Bool) : Bool :=
  let adjT := Tree.build [] K adj
  let colT := Tree.build false K col
  let lev := Tree.build 0 K (levelOf K adjT D)
  (List.range n).all fun u =>
    decide ((Tree.get [] K adjT u).length ≤ d) &&
    (Tree.get [] K adjT u).all (fun v =>
      (Tree.get [] K adjT v.val).any (fun w => w.val == u) &&
      (Tree.get false K colT u != Tree.get false K colT v.val)) &&
    (Tree.get 0 K lev u == 2 ^ n - 1)

theorem step_getD {n : ℕ} (K : ℕ) (adjT : Tree (List (Fin n))) (cur : List ℕ) (v : Fin n) :
    (step K adjT cur).getD v.val 0 =
      (Tree.get [] K adjT v.val).foldl (fun acc u => acc ||| Tree.get 0 K (Tree.build 0 K cur) u.val)
        (Tree.get 0 K (Tree.build 0 K cur) v.val) := by
  simp [step, List.getD_eq_getElem?_getD]

/-- Every `Fin n` index is inside `2 ^ K` when `n ≤ 2 ^ K`. -/
theorem fin_lt_pow {n K : ℕ} (hK : n ≤ 2 ^ K) (v : Fin n) : v.val < 2 ^ K :=
  lt_of_lt_of_le v.isLt hK

theorem get_build_fin {n K : ℕ} (hK : n ≤ 2 ^ K) {α : Type} (d : α) (xs : List α) (v : Fin n) :
    Tree.get d K (Tree.build d K xs) v.val = xs.getD v.val d :=
  get_build d K xs v.val (fin_lt_pow hK v)

theorem levelOf_getD {n K : ℕ} (adj : List (List (Fin n))) (hK : n ≤ 2 ^ K) :
    ∀ (r : ℕ) (v : Fin n),
      (levelOf K (Tree.build [] K adj) r).getD v.val 0 =
        BipartiteDD.ball (fun u : Fin n => adj.getD u.val []) r v := by
  intro r
  induction r with
  | zero =>
    intro v
    simp [levelOf, level0, BipartiteDD.ball, List.getD_eq_getElem?_getD]
  | succ r ih =>
    intro v
    rw [levelOf, step_getD, BipartiteDD.ball]
    simp only [get_build_fin hK, ih]

/-- The fast check gives the spec that `check` tests, vertex by vertex. -/
theorem check_of_spec {n : ℕ} (d D : ℕ) (nbrs : Fin n → List (Fin n)) (color : Fin n → Bool)
    (h : ∀ u, (nbrs u).length ≤ d ∧ (∀ v ∈ nbrs u, u ∈ nbrs v ∧ color u ≠ color v) ∧
      BipartiteDD.ball nbrs D u = 2 ^ n - 1) :
    BipartiteDD.check d D nbrs color = true := by
  simp only [BipartiteDD.check, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, List.mem_finRange, bne_iff_ne, ne_eq, true_implies]
  intro u
  obtain ⟨h1, h2, h3⟩ := h u
  refine ⟨⟨h1, fun v hv => ?_⟩, h3⟩
  simpa using h2 v hv

/-- Soundness of the fast check: a passing `checkFast` gives a passing `check` on the same data. -/
theorem check_of_fast {n : ℕ} (K d D : ℕ) (adj : List (List (Fin n))) (col : List Bool)
    (hK : n ≤ 2 ^ K) (h : checkFast K d D adj col = true) :
    BipartiteDD.check d D (fun u : Fin n => adj.getD u.val [])
      (fun u : Fin n => col.getD u.val false) = true := by
  apply check_of_spec
  intro u
  have hu := (List.all_eq_true.mp h) u.val (List.mem_range.mpr u.isLt)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.any_eq_true,
    bne_iff_ne, ne_eq] at hu
  obtain ⟨⟨h1, h2⟩, h3⟩ := hu
  have hadj : ∀ v : Fin n, Tree.get [] K (Tree.build [] K adj) v.val = adj.getD v.val [] :=
    fun v => get_build_fin hK _ _ v
  have hcol : ∀ v : Fin n, Tree.get false K (Tree.build false K col) v.val = col.getD v.val false :=
    fun v => get_build_fin hK _ _ v
  have hball : ∀ v : Fin n, Tree.get 0 K (Tree.build 0 K (levelOf K (Tree.build [] K adj) D)) v.val
      = BipartiteDD.ball (fun u : Fin n => adj.getD u.val []) D v := by
    intro v
    rw [get_build_fin hK, levelOf_getD adj hK]
  simp only [hadj, hcol, hball] at h1 h2 h3
  refine ⟨h1, fun v hv => ?_, h3⟩
  obtain ⟨⟨w, hw, hwu⟩, hc⟩ := h2 v hv
  have hwu' : w = u := Fin.ext hwu
  subst hwu'
  exact ⟨hw, hc⟩

end BipartiteDD.Fast
