import BipartiteDD.LeanMaxx.Omega45b.Defs

/-!
# Omega45b.Zcount: zero counts of diagonal quadratic forms over `F7`

`wzeros w` is the number of zeros of `Σ w_i x_i²` on `F7^n`.  We prove the exact value `7^4` for five
variables with `0` or `2` zero weights, and the bound `385` for four variables with `0`, `1` or `3`
zero weights.

Method: `cnt w t` counts solutions of `Σ w_i x_i² = t`; peeling off one variable gives
`cnt w t = Σ_a cnt (tail w) (t - w 0 a²)`.  This is a table recursion `tab : List F7 → List ℕ`
(value distribution), proved equal to `cnt`, and the finite checks over all weight vectors are done
by kernel computation.
-/

namespace BipartiteDD.LeanMaxx.Omega45b

/-- number of zero vectors of the diagonal quadratic form Σ w_i x_i² on F7^n -/
def wzeros {n : ℕ} (w : Fin n → F7) : ℕ :=
  (Finset.univ.filter fun x : Fin n → F7 => ∑ i, w i * x i ^ 2 = 0).card
/-- number of zero weights -/
def nzero {n : ℕ} (w : Fin n → F7) : ℕ := (Finset.univ.filter fun i => w i = 0).card

/-- number of solutions of `Σ w_i x_i² = t`. -/
def cnt {n : ℕ} (w : Fin n → F7) (t : F7) : ℕ :=
  (Finset.univ.filter fun x : Fin n → F7 => ∑ i, w i * x i ^ 2 = t).card

lemma cnt_zero (w : Fin 0 → F7) (t : F7) : cnt w t = if t = 0 then 1 else 0 := by
  unfold cnt
  simp [eq_comm]
  split_ifs <;> simp_all

lemma cnt_succ {n : ℕ} (w : Fin (n + 1) → F7) (t : F7) :
    cnt w t = ∑ a : F7, cnt (Fin.tail w) (t - w 0 * a ^ 2) := by
  unfold cnt
  rw [Finset.card_filter, ← Fintype.sum_equiv (Fin.consEquiv (fun _ => F7)) _ _ (fun _ => rfl),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  have : (∑ i : Fin (n + 1), w i * (Fin.consEquiv (fun _ => F7) (a, x)) i ^ 2)
      = w 0 * a ^ 2 + ∑ i : Fin n, Fin.tail w i * x i ^ 2 := by
    rw [Fin.sum_univ_succ]; simp [Fin.consEquiv, Fin.tail]
  rw [this]
  congr 1
  apply propext
  constructor <;> intro h <;> linear_combination h

/-- One convolution step on value tables. -/
def step (c : F7) (v : List ℕ) : List ℕ :=
  (List.range 7).map fun k : ℕ => ∑ a : F7, v.getD (((k : ℕ) : F7) - c * a ^ 2).val 0

/-- Value table of `Σ w_i x_i²` for a list of weights. -/
def tab : List F7 → List ℕ
  | [] => [1, 0, 0, 0, 0, 0, 0]
  | c :: l => step c (tab l)

lemma tab_cnt : ∀ {n : ℕ} (w : Fin n → F7) (t : F7), cnt w t = (tab (List.ofFn w)).getD t.val 0 := by
  intro n
  induction n with
  | zero =>
    intro w t
    rw [cnt_zero]
    simp only [List.ofFn_zero, tab]
    revert t; decide
  | succ n ih =>
    intro w t
    rw [cnt_succ, List.ofFn_succ, tab, step]
    simp only [ih]
    have ht : t.val < 7 := ZMod.val_lt t
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht]
    simp
    rfl

lemma wzeros_eq {n : ℕ} (w : Fin n → F7) : wzeros w = (tab (List.ofFn w)).getD 0 0 := by
  have := tab_cnt w 0
  simpa [cnt, wzeros] using this

/-- Square class representative: `0`, `1` (squares `1,2,4`) or `3` (non-squares `3,5,6`). -/
def cls (c : F7) : F7 := if c = 0 then 0 else if c = 1 ∨ c = 2 ∨ c = 4 then 1 else 3

lemma cls_ex : ∀ c : F7, c ≠ 0 → ∃ u : F7, u ≠ 0 ∧ c = cls c * u ^ 2 := by decide

lemma cls_zero_iff : ∀ c : F7, cls c = 0 ↔ c = 0 := by decide

lemma cls_mem : ∀ c : F7, ∃ i : Fin 3, cls c = ![0, 1, 3] i := by decide

lemma step_scale (c u : F7) (hu : u ≠ 0) (v : List ℕ) : step (c * u ^ 2) v = step c v := by
  unfold step
  refine List.map_congr_left fun k _ => ?_
  refine Fintype.sum_equiv (Equiv.mulLeft₀ u hu) _ _ fun a => ?_
  show v.getD (((k : ℕ) : F7) - c * u ^ 2 * a ^ 2).val 0
    = v.getD (((k : ℕ) : F7) - c * (u * a) ^ 2).val 0
  congr 3
  ring

lemma step_cls (c : F7) (v : List ℕ) : step (cls c) v = step c v := by
  by_cases hc : c = 0
  · simp [cls, hc]
  · obtain ⟨u, hu, h⟩ := cls_ex c hc
    conv_rhs => rw [h]
    exact (step_scale _ u hu v).symm

lemma tab_map_cls : ∀ l : List F7, tab (l.map cls) = tab l
  | [] => rfl
  | c :: l => by simp only [List.map_cons, tab, step_cls, tab_map_cls l]

lemma wzeros_cls {n : ℕ} (w : Fin n → F7) : wzeros (cls ∘ w) = wzeros w := by
  rw [wzeros_eq, wzeros_eq, ← List.map_ofFn, tab_map_cls]

lemma nzero_cls {n : ℕ} (w : Fin n → F7) : nzero (cls ∘ w) = nzero w := by
  unfold nzero
  simp [Function.comp, cls_zero_iff]

lemma key5 : ∀ i j k l m : Fin 3,
    (nzero ![![0, 1, 3] i, ![0, 1, 3] j, ![0, 1, 3] k, ![0, 1, 3] l, ![0, 1, 3] m] = 0 ∨
     nzero ![![0, 1, 3] i, ![0, 1, 3] j, ![0, 1, 3] k, ![0, 1, 3] l, ![0, 1, 3] m] = 2) →
      (tab [![0, 1, 3] i, ![0, 1, 3] j, ![0, 1, 3] k, ![0, 1, 3] l, ![0, 1, 3] m]).getD 0 0
        = 2401 := by decide +kernel

lemma key4 : ∀ i j k l : Fin 3,
    (nzero ![![0, 1, 3] i, ![0, 1, 3] j, ![0, 1, 3] k, ![0, 1, 3] l] = 0 ∨
     nzero ![![0, 1, 3] i, ![0, 1, 3] j, ![0, 1, 3] k, ![0, 1, 3] l] = 1 ∨
     nzero ![![0, 1, 3] i, ![0, 1, 3] j, ![0, 1, 3] k, ![0, 1, 3] l] = 3) →
      (tab [![0, 1, 3] i, ![0, 1, 3] j, ![0, 1, 3] k, ![0, 1, 3] l]).getD 0 0 ≤ 385 := by
  decide +kernel

theorem wzeros5 (w : Fin 5 → F7) (h : nzero w = 0 ∨ nzero w = 2) : wzeros w = 2401 := by
  obtain ⟨i, hi⟩ := cls_mem (w 0)
  obtain ⟨j, hj⟩ := cls_mem (w 1)
  obtain ⟨k, hk⟩ := cls_mem (w 2)
  obtain ⟨l, hl⟩ := cls_mem (w 3)
  obtain ⟨m, hm⟩ := cls_mem (w 4)
  have hw : cls ∘ w = ![![0, 1, 3] i, ![0, 1, 3] j, ![0, 1, 3] k, ![0, 1, 3] l, ![0, 1, 3] m] := by
    ext x; fin_cases x <;> simp [hi, hj, hk, hl, hm]
  rw [← wzeros_cls, hw, wzeros_eq]
  rw [← nzero_cls, hw] at h
  exact key5 i j k l m h

theorem wzeros4 (w : Fin 4 → F7) (h : nzero w = 0 ∨ nzero w = 1 ∨ nzero w = 3) : wzeros w ≤ 385 := by
  obtain ⟨i, hi⟩ := cls_mem (w 0)
  obtain ⟨j, hj⟩ := cls_mem (w 1)
  obtain ⟨k, hk⟩ := cls_mem (w 2)
  obtain ⟨l, hl⟩ := cls_mem (w 3)
  have hw : cls ∘ w = ![![0, 1, 3] i, ![0, 1, 3] j, ![0, 1, 3] k, ![0, 1, 3] l] := by
    ext x; fin_cases x <;> simp [hi, hj, hk, hl]
  rw [← wzeros_cls, hw, wzeros_eq]
  rw [← nzero_cls, hw] at h
  exact key4 i j k l h

end BipartiteDD.LeanMaxx.Omega45b
