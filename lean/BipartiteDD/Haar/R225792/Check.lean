import BipartiteDD.Haar.R225792.Tables

/-! The covering certificates of the record Δ8·D8 on 225,792 vertices (job d8D8).

An element of `G8` is given by indices `(i, j, z)`: PSL index, SL index, Z/2 index. A word code `w` holds eight
letters, letter `t` being the `t`-th base-8 digit of `w`; each letter is an index into `S`. The words are
multiplied on indices with the tables of `TabData.lean`, and `toG` maps the result to `G8`. Stage `k` holds the
certificates of the elements with PSL index in `[6k, 6k+6)`; element `t` of the stage is
`(i, j, z) = (6k + t / 672, (t % 672) / 2, t % 2)`. -/

namespace BipartiteDD.Haar.R225792

open M2

/-- An element of `G8` by indices. -/
abbrev Ix := ℕ × ℕ × ℕ

/-- The element of `G8` with the given indices. -/
def toG (x : Ix) : G8 := (fP (f168 x.1), fS (f336 x.2.1), fZ (f2 x.2.2))

def mulI (x y : Ix) : Ix := (mP x.1 y.1, mQ x.2.1 y.2.1, (x.2.2 + y.2.2) % 2)

def invI (x : Ix) : Ix := (iP x.1, iQ x.2.1, x.2.2)

def k8 (k : ℕ) : Fin 8 := ⟨k % 8, Nat.mod_lt _ (by norm_num)⟩

/-- The letter `k` of `S`, by indices. -/
def sI (k : ℕ) : Ix := ((sPi (k8 k)).val, (sQj (k8 k)).val, (sZk (k8 k)).val)

/-- The letter `k` of `S`, as an element of `G8`. -/
def sS (k : Fin 8) : G8 := (fP (sPi k), fS (sQj k), fZ (sZk k))

def sN (k : ℕ) : G8 := sS (k8 k)

/-- The `t`-th letter of the word code `w`. -/
def letter (w t : ℕ) : ℕ := w / 8 ^ t % 8

/-- `s₁⁻¹ s₂ s₃⁻¹ s₄ s₅⁻¹ s₆ s₇⁻¹ s₈` in `G8`. -/
def prodA (w : ℕ) : G8 :=
  (sN (letter w 0))⁻¹ * sN (letter w 1) * (sN (letter w 2))⁻¹ * sN (letter w 3) *
    (sN (letter w 4))⁻¹ * sN (letter w 5) * (sN (letter w 6))⁻¹ * sN (letter w 7)

/-- `s₁ s₂⁻¹ s₃ s₄⁻¹ s₅ s₆⁻¹ s₇ s₈⁻¹` in `G8`. -/
def prodB (w : ℕ) : G8 :=
  sN (letter w 0) * (sN (letter w 1))⁻¹ * sN (letter w 2) * (sN (letter w 3))⁻¹ *
    sN (letter w 4) * (sN (letter w 5))⁻¹ * sN (letter w 6) * (sN (letter w 7))⁻¹

/-- `s₁ s₂⁻¹ s₃ s₄⁻¹ s₅ s₆⁻¹ s₇` in `G8`. -/
def prodC (w : ℕ) : G8 :=
  sN (letter w 0) * (sN (letter w 1))⁻¹ * sN (letter w 2) * (sN (letter w 3))⁻¹ *
    sN (letter w 4) * (sN (letter w 5))⁻¹ * sN (letter w 6)

/-- The three words of `w` by indices. -/
def prodIA (w : ℕ) : Ix :=
  mulI (mulI (mulI (mulI (mulI (mulI (mulI (invI (sI (letter w 0))) (sI (letter w 1)))
    (invI (sI (letter w 2)))) (sI (letter w 3))) (invI (sI (letter w 4)))) (sI (letter w 5)))
    (invI (sI (letter w 6)))) (sI (letter w 7))

def prodIB (w : ℕ) : Ix :=
  mulI (mulI (mulI (mulI (mulI (mulI (mulI (sI (letter w 0)) (invI (sI (letter w 1))))
    (sI (letter w 2))) (invI (sI (letter w 3)))) (sI (letter w 4))) (invI (sI (letter w 5))))
    (sI (letter w 6))) (invI (sI (letter w 7)))

def prodIC (w : ℕ) : Ix :=
  mulI (mulI (mulI (mulI (mulI (mulI (sI (letter w 0)) (invI (sI (letter w 1))))
    (sI (letter w 2))) (invI (sI (letter w 3)))) (sI (letter w 4))) (invI (sI (letter w 5))))
    (sI (letter w 6))

/-! Links between the tables and the group `G8`. -/

theorem mP_spec (i j : ℕ) : pslAt (f168 (mP i j)) = canon (mul (pslAt (f168 i)) (pslAt (f168 j))) := by
  have h := mP_ok (i % 168) (Nat.mod_lt _ (by norm_num))
  unfold mPcheck at h
  rw [List.all_eq_true] at h
  have hj := h (j % 168) (List.mem_range.2 (Nat.mod_lt _ (by norm_num)))
  simp only [decide_eq_true_eq] at hj
  have e1 : mP i j = mP (i % 168) (j % 168) := by simp [mP, Nat.mod_mod]
  have e2 : f168 (i % 168) = f168 i := Fin.ext (by simp [f168, Nat.mod_mod])
  have e3 : f168 (j % 168) = f168 j := Fin.ext (by simp [f168, Nat.mod_mod])
  rw [e1, ← e2, ← e3]
  exact hj

theorem mQ_spec (i j : ℕ) : slAt (f336 (mQ i j)) = mul (slAt (f336 i)) (slAt (f336 j)) := by
  have h := mQ_ok (i % 336) (Nat.mod_lt _ (by norm_num))
  unfold mQcheck at h
  rw [List.all_eq_true] at h
  have hj := h (j % 336) (List.mem_range.2 (Nat.mod_lt _ (by norm_num)))
  simp only [decide_eq_true_eq] at hj
  have e1 : mQ i j = mQ (i % 336) (j % 336) := by simp [mQ, Nat.mod_mod]
  have e2 : f336 (i % 336) = f336 i := Fin.ext (by simp [f336, Nat.mod_mod])
  have e3 : f336 (j % 336) = f336 j := Fin.ext (by simp [f336, Nat.mod_mod])
  rw [e1, ← e2, ← e3]
  exact hj

theorem iP_spec (i : ℕ) : pslAt (f168 (iP i)) = canon (adj (pslAt (f168 i))) := by
  have h := iP_ok (i % 168) (Nat.mod_lt _ (by norm_num))
  unfold iPcheck at h
  simp only [decide_eq_true_eq] at h
  have e1 : iP i = iP (i % 168) := by simp [iP, Nat.mod_mod]
  have e2 : f168 (i % 168) = f168 i := Fin.ext (by simp [f168, Nat.mod_mod])
  rw [e1, ← e2]
  exact h

theorem iQ_spec (j : ℕ) : slAt (f336 (iQ j)) = adj (slAt (f336 j)) := by
  have h := iQ_ok (j % 336) (Nat.mod_lt _ (by norm_num))
  unfold iQcheck at h
  simp only [decide_eq_true_eq] at h
  have e1 : iQ j = iQ (j % 336) := by simp [iQ, Nat.mod_mod]
  have e2 : f336 (j % 336) = f336 j := Fin.ext (by simp [f336, Nat.mod_mod])
  rw [e1, ← e2]
  exact h

theorem fP_mul (i j : ℕ) : fP (f168 (mP i j)) = fP (f168 i) * fP (f168 j) :=
  Subtype.ext (mP_spec i j)

theorem fS_mul (i j : ℕ) : fS (f336 (mQ i j)) = fS (f336 i) * fS (f336 j) :=
  Subtype.ext (mQ_spec i j)

theorem fP_iP (i : ℕ) : fP (f168 (iP i)) = (fP (f168 i))⁻¹ :=
  Subtype.ext (iP_spec i)

theorem fS_iQ (j : ℕ) : fS (f336 (iQ j)) = (fS (f336 j))⁻¹ :=
  Subtype.ext (iQ_spec j)

theorem zmod2_neg (a : ZMod 2) : -a = a := by
  revert a
  decide

theorem fZ_mul (a b : ℕ) : fZ (f2 ((a + b) % 2)) = fZ (f2 a) * fZ (f2 b) := by
  unfold fZ f2
  rw [← ofAdd_add]
  congr 1
  simp [ZMod.natCast_mod, Nat.cast_add]

theorem fZ_inv_eq (a : ℕ) : (fZ (f2 a))⁻¹ = fZ (f2 a) := by
  unfold fZ
  rw [← ofAdd_neg, zmod2_neg]

theorem toG_mulI (x y : Ix) : toG (mulI x y) = toG x * toG y := by
  simp only [toG, mulI, Prod.mk_mul_mk, fP_mul, fS_mul, fZ_mul]

theorem toG_invI (x : Ix) : toG (invI x) = (toG x)⁻¹ := by
  simp only [toG, invI, Prod.inv_mk, fP_iP, fS_iQ, fZ_inv_eq]

theorem toG_sI (k : ℕ) : toG (sI k) = sN k := by
  simp [toG, sI, sN, sS, f168_val, f336_val, f2_val]

theorem toG_prodIA (w : ℕ) : toG (prodIA w) = prodA w := by
  simp only [prodIA, prodA, toG_mulI, toG_invI, toG_sI]

theorem toG_prodIB (w : ℕ) : toG (prodIB w) = prodB w := by
  simp only [prodIB, prodB, toG_mulI, toG_invI, toG_sI]

theorem toG_prodIC (w : ℕ) : toG (prodIC w) = prodC w := by
  simp only [prodIC, prodC, toG_mulI, toG_invI, toG_sI]

/-! The check of one element, and of one stage. -/

/-- The check of the element `(i, j, z)`: its three words, read from the 72-bit block `cc`. -/
def checkOneI (i j z cc : ℕ) : Bool :=
  decide (prodIA (cc % 2 ^ 24) = (i, j, z)) && decide (prodIB (cc / 2 ^ 24 % 2 ^ 24) = (i, j, z)) &&
    decide (prodIC (cc / 2 ^ 48 % 2 ^ 24) = (i, j, z))

/-- The check of the blocks of a stage list, from element `t` on; one pass over the list. -/
def checkRec (k : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | t, cc :: rest => checkOneI (6 * k + t / 672) (t % 672 / 2) (t % 2) cc && checkRec k (t + 1) rest

/-- The check of one chunk `l` of a stage, its first element being element `252 * c`. -/
def checkChunk (k c : ℕ) (l : List ℕ) : Bool :=
  checkRec k (252 * c) l && decide (l.length = 252)

theorem checkRec_sound (k : ℕ) : ∀ (l : List ℕ) (s : ℕ), checkRec k s l = true →
    ∀ (idx : ℕ) (h : idx < l.length),
      checkOneI (6 * k + (s + idx) / 672) ((s + idx) % 672 / 2) ((s + idx) % 2) (l[idx]) = true := by
  intro l
  induction l with
  | nil => intro s _ idx h; simp at h
  | cons cc rest ih =>
    intro s hrec idx h
    unfold checkRec at hrec
    simp only [Bool.and_eq_true] at hrec
    cases idx with
    | zero => simpa using hrec.1
    | succ n =>
      have := ih (s + 1) hrec.2 n (by simpa using h)
      have e : s + (n + 1) = s + 1 + n := by omega
      simpa [e] using this

/-- A passing chunk gives the check of each of its elements, read from the stage list `l`:
element `t` (with `t / 252 = c`) has its block `l.getD t 0`. -/
theorem chunk_elem {k c t : ℕ} {l : List ℕ} (hc : checkChunk k c ((l.drop (252 * c)).take 252) = true)
    (ht : t / 252 = c) :
    checkOneI (6 * k + t / 672) (t % 672 / 2) (t % 2) (l.getD t 0) = true := by
  unfold checkChunk at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  have htl : t < l.length := by
    have h2 := hc.2
    rw [List.length_take, List.length_drop] at h2
    omega
  have hidx : t - 252 * c < ((l.drop (252 * c)).take 252).length := by
    rw [hc.2]; omega
  have hs := checkRec_sound k _ (252 * c) hc.1 (t - 252 * c) hidx
  have e1 : 252 * c + (t - 252 * c) = t := by omega
  rw [e1] at hs
  have hget : ((l.drop (252 * c)).take 252)[t - 252 * c] = l.getD t 0 := by
    rw [List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl]
    simp only [Option.getD_some]
    simp [e1]
  rw [hget] at hs
  exact hs

end BipartiteDD.Haar.R225792
