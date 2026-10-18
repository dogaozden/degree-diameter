import BipartiteDD.Fast

/-! Staged checking, for graphs too large for one kernel evaluation of `checkFast`.

`checkFast` computes all `D` radii of ball masks inside one kernel check, so the kernel's memory
grows with the whole computation. Here the masks of radius `r` are data, `chainL n D levs r`. Each
stage `stepOK` checks one radius step: the masks of radius `r + 1` are the step of those of radius
`r`. Every stage is its own declaration (and module), so the kernel memory is that of one step.
Nothing in the data is trusted: the stages verify it. `check_of_chain` then gives the same conclusion
as `check_of_fast`. -/

namespace BipartiteDD.Staged

open BipartiteDD.Fast

/-- The local part of `checkFast`: degrees, symmetry and colouring. -/
def checkLocal (K d : ℕ) {n : ℕ} (adj : List (List (Fin n))) (col : List Bool) : Bool :=
  let adjT := Tree.build [] K adj
  let colT := Tree.build false K col
  (List.range n).all fun u =>
    decide ((Tree.get [] K adjT u).length ≤ d) &&
    (Tree.get [] K adjT u).all (fun v =>
      (Tree.get [] K adjT v.val).any (fun w => w.val == u) &&
      (Tree.get false K colT u != Tree.get false K colT v.val))

/-- The local test of `checkLocal` restricted to the vertices `lo ≤ u < hi`, so that a large graph's
local test can be kernel-checked in pieces. -/
def localRange (K d lo hi : ℕ) {n : ℕ} (adj : List (List (Fin n))) (col : List Bool) : Bool :=
  let adjT := Tree.build [] K adj
  let colT := Tree.build false K col
  (List.range' lo (hi - lo)).all fun u =>
    decide ((Tree.get [] K adjT u).length ≤ d) &&
    (Tree.get [] K adjT u).all (fun v =>
      (Tree.get [] K adjT v.val).any (fun w => w.val == u) &&
      (Tree.get false K colT u != Tree.get false K colT v.val))

/-- The local test on `lo ≤ u < hi` and on `hi ≤ u < hi'` give it on `lo ≤ u < hi'`. -/
theorem localRange_append {K d lo m hi n : ℕ} {adj : List (List (Fin n))} {col : List Bool}
    (h1 : localRange K d lo m adj col = true) (h2 : localRange K d m hi adj col = true)
    (hlm : lo ≤ m) (hmh : m ≤ hi) : localRange K d lo hi adj col = true := by
  simp only [localRange] at h1 h2 ⊢
  rw [List.all_eq_true] at h1 h2 ⊢
  intro u hu
  rw [List.mem_range'_1] at hu
  by_cases hum : u < m
  · exact h1 u (List.mem_range'_1.mpr ⟨hu.1, by omega⟩)
  · exact h2 u (List.mem_range'_1.mpr ⟨by omega, by omega⟩)

/-- The local test of all `n` vertices, from its restriction to `0 ≤ u < n`. -/
theorem checkLocal_of_range {K d n : ℕ} {adj : List (List (Fin n))} {col : List Bool}
    (h : localRange K d 0 n adj col = true) : checkLocal K d adj col = true := by
  simp only [localRange, checkLocal, Nat.sub_zero] at h ⊢
  rw [List.range_eq_range']
  exact h

/-- One radius step: `nxt` is the step of `cur`. -/
def stepOK (K : ℕ) {n : ℕ} (adj : List (List (Fin n))) (cur nxt : List ℕ) : Bool :=
  decide (step K (Tree.build [] K adj) cur = nxt)

/-- The masks of radius `r`: `level0` at `0`, the full masks at `D`, and the stored `levs` between.
`levs.getD (r - 1)` is the stored radius `r`. -/
def chainL (n D : ℕ) (levs : List (List ℕ)) (r : ℕ) : List ℕ :=
  if r = 0 then level0 n else if r = D then List.replicate n (2 ^ n - 1) else levs.getD (r - 1) []

theorem of_stepOK {K n : ℕ} {adj : List (List (Fin n))} {cur nxt : List ℕ}
    (h : stepOK K adj cur nxt = true) : step K (Tree.build [] K adj) cur = nxt :=
  of_decide_eq_true h

/-- A chain of levels that starts at `level0` and takes one step at a time is the true `levelOf`. -/
theorem levelOf_eq_chain {n : ℕ} (K : ℕ) (adjT : Tree (List (Fin n))) (L : ℕ → List ℕ) (D : ℕ)
    (h0 : L 0 = level0 n) (hs : ∀ r < D, step K adjT (L r) = L (r + 1)) :
    ∀ r ≤ D, levelOf K adjT r = L r := by
  intro r
  induction r with
  | zero => intro _; rw [levelOf, h0]
  | succ r ih =>
    intro hr
    rw [levelOf, ih (by omega), hs r (by omega)]

/-- If the chain ends at the full masks, every ball of radius `D` is full. -/
theorem ball_full_of_chain {n K D : ℕ} (adj : List (List (Fin n))) (hK : n ≤ 2 ^ K)
    (L : ℕ → List ℕ) (h0 : L 0 = level0 n)
    (hs : ∀ r < D, step K (Tree.build [] K adj) (L r) = L (r + 1))
    (hD : L D = List.replicate n (2 ^ n - 1)) (u : Fin n) :
    BipartiteDD.ball (fun u : Fin n => adj.getD u.val []) D u = 2 ^ n - 1 := by
  rw [← levelOf_getD adj hK D u, levelOf_eq_chain K _ L D h0 hs D le_rfl, hD]
  simp [List.getD_eq_getElem?_getD, u.isLt]

/-- The staged check gives the same conclusion as `check_of_fast`. -/
theorem check_of_chain {n : ℕ} (K d D : ℕ) (adj : List (List (Fin n))) (col : List Bool)
    (hK : n ≤ 2 ^ K) (levs : List (List ℕ)) (hD0 : 0 < D)
    (hloc : checkLocal K d adj col = true)
    (hstep : ∀ r < D, stepOK K adj (chainL n D levs r) (chainL n D levs (r + 1)) = true) :
    BipartiteDD.check d D (fun u : Fin n => adj.getD u.val [])
      (fun u : Fin n => col.getD u.val false) = true := by
  have hs : ∀ r < D, step K (Tree.build [] K adj) (chainL n D levs r) = chainL n D levs (r + 1) :=
    fun r hr => of_stepOK (hstep r hr)
  have h0 : chainL n D levs 0 = level0 n := by simp [chainL]
  have hD : chainL n D levs D = List.replicate n (2 ^ n - 1) := by
    simp [chainL, hD0.ne']
  apply check_of_spec
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
  refine ⟨h1, fun v hv => ?_, ball_full_of_chain adj hK _ h0 hs hD u⟩
  obtain ⟨⟨w, hw, hwu⟩, hc⟩ := h2 v hv
  have hwu' : w = u := Fin.ext hwu
  subst hwu'
  exact ⟨hw, hc⟩

end BipartiteDD.Staged
