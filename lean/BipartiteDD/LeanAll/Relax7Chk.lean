import BipartiteDD.LeanAll.Relax7

/-! # Checks for `Relax7.main7`

* `ph2OK` (points) and `lh2OK` (lines): a freed set whose elements have at most one partner. As in `TypedHex.rhOK`,
  every freed point lists its `p + 1` lines, all in a global line table sorted by Plücker code; a table line has
  owners `go1, go2` (equal when it has one), and both owners of every line of `r` are `r` or its partner `pr r`. So a
  point collinear with `r` is `pr r` (`ph2_part`).
* `hubChk`: the two hubs of a paired element, with the incidences of their other slots with the partner (`hh_of`). -/

namespace BipartiteDD.LeanAll.Relax7

open BipartiteDD BipartiteDD.Hexagon BipartiteDD.HexagonD7 BipartiteDD.LeanAll.HexArith BipartiteDD.LeanAll.Orbit2
open BipartiteDD.LeanAll.HexLocal BipartiteDD.LeanAll.Typed BipartiteDD.LeanAll.TypedHex BipartiteDD.LeanAll.TypedHex5
open SimpleGraph Finset
open scoped Classical

set_option linter.unusedSectionVars false

variable {p : ℕ} [Fact p.Prime]

/-! ## Freed points with partners -/

/-- Freed point `r` (code `rhc r`, partner `pr r`) with its lines in the global table `gA, gB` (owners `go1, go2`). -/
def ph2OK (p nH nG : ℕ) (rhc pr go1 go2 gA gB : ℕ → ℕ) (ents : ℕ → List (ℕ × ℕ × ℕ)) (r : ℕ) : Bool :=
  ptOKb p (rhc r) && (Nat.beq (r + 1) nH || Nat.blt (rhc r) (rhc (r + 1))) && Nat.beq (lenP (ents r)) (p + 1) &&
    sortedLt ((ents r).map (·.1)) && Nat.blt (pr r) nH &&
    allP (fun t => Nat.blt t.1 nG && (Nat.beq (go1 t.1) r || Nat.beq (go2 t.1) r) &&
      (Nat.beq (go1 t.1) r || Nat.beq (go1 t.1) (pr r)) && (Nat.beq (go2 t.1) r || Nat.beq (go2 t.1) (pr r)) &&
      linN p (rhc r) (gA t.1) (gB t.1) t.2.1 t.2.2) (ents r)

section Points

variable {nH nG : ℕ} {rhc pr go1 go2 gA gB : ℕ → ℕ} {ents : ℕ → List (ℕ × ℕ × ℕ)}

theorem ph2_pt (h : ∀ r < nH, ph2OK p nH nG rhc pr go1 go2 gA gB ents r = true) : ∀ r < nH, PtOK p (rhc r) := by
  intro r hr; have := h r hr; simp only [ph2OK, Bool.and_eq_true] at this; exact ptOKb_spec this.1.1.1.1.1

theorem ph2_pr (h : ∀ r < nH, ph2OK p nH nG rhc pr go1 go2 gA gB ents r = true) : ∀ r < nH, pr r < nH := by
  intro r hr; have := h r hr; simp only [ph2OK, Bool.and_eq_true, Nat.blt_eq] at this; exact this.1.2

theorem ph2_inj (h : ∀ r < nH, ph2OK p nH nG rhc pr go1 go2 gA gB ents r = true) :
    ∀ r < nH, ∀ r' < nH, ptOf p (rhc r) = ptOf p (rhc r') → r = r' := by
  intro r hr r' hr' he
  have hinc : ∀ r, r + 1 < nH → rhc r < rhc (r + 1) := by
    intro r hr; have := h r (by omega); simp only [ph2OK, Bool.and_eq_true] at this
    exact ltOfBlt (succ_of this.1.1.1.1.2 hr)
  exact inj_of_succ hinc r hr r' hr' (ptOf_inj (ph2_pt h r hr) (ph2_pt h r' hr') he)

/-- A point collinear with a freed point `r` is its partner. -/
theorem ph2_part (h : ∀ r < nH, ph2OK p nH nG rhc pr go1 go2 gA gB ents r = true)
    (hg : ∀ e < nG, glOK p nG gA gB e = true) :
    ∀ r < nH, ∀ s < nH, Coll hexInc (ptOf p (rhc r)) (ptOf p (rhc s)) → s = pr r := by
  have key : ∀ r < nH, ∀ W, hexInc (ptOf p (rhc r)) W →
      ∃ e < nG, (go1 e = r ∨ go2 e = r) ∧ (go1 e = r ∨ go1 e = pr r) ∧ (go2 e = r ∨ go2 e = pr r) ∧
        W = lineOf p (gA e) (gB e) := by
    intro r hr W hW
    have hr' := h r hr
    simp only [ph2OK, Bool.and_eq_true, Nat.beq_eq, lenP_eq, allP_eq, List.all_eq_true, Nat.blt_eq,
      Bool.or_eq_true] at hr'
    obtain ⟨⟨⟨⟨⟨-, -⟩, hlen⟩, hsrt⟩, -⟩, hent⟩ := hr'
    have hmem : W ∈ (ents r).map (fun t => lineOf p (gA t.1) (gB t.1)) := by
      refine mem_of_card (card_lns _) _ (by rw [List.length_map, hlen]) ?_ ?_ W hW
      · exact nodup_map_of (nodup_of_sortedLt hsrt) (fun t ht t' ht' htt =>
          gl_inj hg _ (hent t ht).1.1.1.1 _ (hent t' ht').1.1.1.1 htt)
      · intro W' hW'
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hW'
        exact inc_of_lin (ph2_pt h r hr) (lnOK_of_gl hg _ (hent t ht).1.1.1.1) (hent t ht).2
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hmem
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩ := hent t ht
    exact ⟨t.1, h1, h2, h3, h4, rfl⟩
  rintro r hr s hs ⟨hne, W, h1, h2⟩
  obtain ⟨e, he, -, hr1, hr2, rfl⟩ := key r hr W h1
  obtain ⟨e', he', hs0, -, -, hee⟩ := key s hs _ h2
  have := gl_inj hg _ he _ he' hee
  subst this
  have hsr : s ≠ r := fun h => hne (by rw [h])
  rcases hs0 with hs0 | hs0
  · rcases hr1 with h | h
    · exact absurd (hs0.symm.trans h) hsr
    · exact hs0.symm.trans h
  · rcases hr2 with h | h
    · exact absurd (hs0.symm.trans h) hsr
    · exact hs0.symm.trans h

end Points

/-! ## Freed lines with partners -/

/-- Freed line `l` (basis `rla l, rlb l`, partner `pr l`) with its points in the global table `gp` (owners `go1, go2`). -/
def lh2OK (p nL nP : ℕ) (rla rlb pr go1 go2 gp : ℕ → ℕ) (ents : ℕ → List (ℕ × ℕ × ℕ)) (l : ℕ) : Bool :=
  lnOKb p (rla l) (rlb l) &&
    (Nat.beq (l + 1) nL || Nat.blt (plCode p (rla l) (rlb l)) (plCode p (rla (l + 1)) (rlb (l + 1)))) &&
    Nat.beq (lenP (ents l)) (p + 1) && sortedLt ((ents l).map (·.1)) && Nat.blt (pr l) nL &&
    allP (fun t => Nat.blt t.1 nP && (Nat.beq (go1 t.1) l || Nat.beq (go2 t.1) l) &&
      (Nat.beq (go1 t.1) l || Nat.beq (go1 t.1) (pr l)) && (Nat.beq (go2 t.1) l || Nat.beq (go2 t.1) (pr l)) &&
      linN p (gp t.1) (rla l) (rlb l) t.2.1 t.2.2) (ents l)

section Lines

variable {nL nP : ℕ} {rla rlb pr go1 go2 gp : ℕ → ℕ} {ents : ℕ → List (ℕ × ℕ × ℕ)}

theorem lh2_ln (h : ∀ l < nL, lh2OK p nL nP rla rlb pr go1 go2 gp ents l = true) :
    ∀ l < nL, LnOK p (rla l) (rlb l) := by
  intro l hl; have := h l hl; simp only [lh2OK, Bool.and_eq_true] at this; exact lnOKb_spec this.1.1.1.1.1

theorem lh2_pr (h : ∀ l < nL, lh2OK p nL nP rla rlb pr go1 go2 gp ents l = true) : ∀ l < nL, pr l < nL := by
  intro l hl; have := h l hl; simp only [lh2OK, Bool.and_eq_true, Nat.blt_eq] at this; exact this.1.2

theorem lh2_inj (h : ∀ l < nL, lh2OK p nL nP rla rlb pr go1 go2 gp ents l = true) :
    ∀ l < nL, ∀ l' < nL, lineOf p (rla l) (rlb l) = lineOf p (rla l') (rlb l') → l = l' := by
  intro l hl l' hl' he
  have hinc : ∀ l, l + 1 < nL → plCode p (rla l) (rlb l) < plCode p (rla (l + 1)) (rlb (l + 1)) := by
    intro l hl; have := h l (by omega); simp only [lh2OK, Bool.and_eq_true] at this
    exact ltOfBlt (succ_of this.1.1.1.1.2 hl)
  exact inj_of_succ (f := fun l => plCode p (rla l) (rlb l)) hinc l hl l' hl'
    (lineOf_inj (lh2_ln h l hl) (lh2_ln h l' hl') he)

/-- A line concurrent with a freed line `l` is its partner. -/
theorem lh2_part (h : ∀ l < nL, lh2OK p nL nP rla rlb pr go1 go2 gp ents l = true)
    (hg : ∀ e < nP, gpOK p nP gp e = true) :
    ∀ l < nL, ∀ s < nL, Conc hexInc (lineOf p (rla l) (rlb l)) (lineOf p (rla s) (rlb s)) → s = pr l := by
  have key : ∀ l < nL, ∀ x, hexInc x (lineOf p (rla l) (rlb l)) →
      ∃ e < nP, (go1 e = l ∨ go2 e = l) ∧ (go1 e = l ∨ go1 e = pr l) ∧ (go2 e = l ∨ go2 e = pr l) ∧
        x = ptOf p (gp e) := by
    intro l hl x hx
    have hl' := h l hl
    simp only [lh2OK, Bool.and_eq_true, Nat.beq_eq, lenP_eq, allP_eq, List.all_eq_true, Nat.blt_eq,
      Bool.or_eq_true] at hl'
    obtain ⟨⟨⟨⟨⟨-, -⟩, hlen⟩, hsrt⟩, -⟩, hent⟩ := hl'
    have hmem : x ∈ (ents l).map (fun t => ptOf p (gp t.1)) := by
      refine mem_of_card (card_pts _) _ (by rw [List.length_map, hlen]) ?_ ?_ x hx
      · exact nodup_map_of (nodup_of_sortedLt hsrt) (fun t ht t' ht' htt =>
          gp_inj hg _ (hent t ht).1.1.1.1 _ (hent t' ht').1.1.1.1 htt)
      · intro x' hx'
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx'
        exact inc_of_lin (ptOK_of_gp hg _ (hent t ht).1.1.1.1) (lh2_ln h l hl) (hent t ht).2
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hmem
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩ := hent t ht
    exact ⟨t.1, h1, h2, h3, h4, rfl⟩
  rintro l hl s hs ⟨hne, x, h1, h2⟩
  obtain ⟨e, he, -, hr1, hr2, rfl⟩ := key l hl x h1
  obtain ⟨e', he', hs0, -, -, hee⟩ := key s hs _ h2
  have := gp_inj hg _ he _ he' hee
  subst this
  have hsr : s ≠ l := fun h => hne (by rw [h])
  rcases hs0 with hs0 | hs0
  · rcases hr1 with h | h
    · exact absurd (hs0.symm.trans h) hsr
    · exact hs0.symm.trans h
  · rcases hr2 with h | h
    · exact absurd (hs0.symm.trans h) hsr
    · exact hs0.symm.trans h

end Lines

/-! ## Slot positions -/

/-- The code at position `pos` of the `A`-slots of level `a`. -/
def cAt (nT : ℕ → ℕ) (cF : ℕ → ℕ → ℕ × ℕ) (a pos : ℕ) : ℕ × ℕ :=
  if pos < nT (trn a 1) then cF (trn a 1) pos
  else if pos < nT (trn a 1) + nT (trn a 2) then cF (trn a 2) (pos - nT (trn a 1))
  else cF (trn a 3) (pos - nT (trn a 1) - nT (trn a 2))

/-- The code at position `pos` of the `B`-slots of level `a`. -/
def cBt (nT : ℕ → ℕ) (cI : ℕ → ℕ → ℕ × ℕ) (a pos : ℕ) : ℕ × ℕ :=
  if pos < nT (trn (src a 1) 1) then cI (trn (src a 1) 1) pos
  else if pos < nT (trn (src a 1) 1) + nT (trn (src a 2) 2) then cI (trn (src a 2) 2) (pos - nT (trn (src a 1) 1))
  else cI (trn (src a 3) 3) (pos - nT (trn (src a 1) 1) - nT (trn (src a 2) 2))

/-- Where the freed set of `a → a + k` starts among the `A`-slots of level `a`. -/
def offA (nT : ℕ → ℕ) (a k : ℕ) : ℕ :=
  if k = 1 then 0 else if k = 2 then nT (trn a 1) else nT (trn a 1) + nT (trn a 2)

/-- Where the images of `src b k → b` start among the `B`-slots of level `b`. -/
def offB (nT : ℕ → ℕ) (b k : ℕ) : ℕ :=
  if k = 1 then 0 else if k = 2 then nT (trn (src b 1) 1) else nT (trn (src b 1) 1) + nT (trn (src b 2) 2)

/-- The number of `A`-slots of level `a`. -/
def lenA (nT : ℕ → ℕ) (a : ℕ) : ℕ := nT (trn a 1) + nT (trn a 2) + nT (trn a 3)

/-- The number of `B`-slots of level `b`. -/
def lenB (nT : ℕ → ℕ) (b : ℕ) : ℕ := nT (trn (src b 1) 1) + nT (trn (src b 2) 2) + nT (trn (src b 3) 3)

section Pos

variable {TY : ℕ → Bool} {nT : ℕ → ℕ} {kF kI : ℕ → Bool} {cF cI : ℕ → ℕ → ℕ × ℕ}

theorem length_Al (a : ℕ) : (Al p nT kF cF a).length = lenA nT a := by
  simp [Al, FL, lenA]; omega

theorem length_Bl (b : ℕ) : (Bl p nT kI cI b).length = lenB nT b := by
  simp [Bl, IL, lenB]; omega

theorem getD_Al (hkF : ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → kF (trn a k) = TY a) {a pos : ℕ} (ha : a < 7)
    (hpos : pos < lenA nT a) : (Al p nT kF cF a).getD pos (dE p) = den p (TY a) (cAt nT cF a pos) := by
  unfold Al FL lst
  rw [getD_app3 _ hpos]
  unfold cAt
  rw [hkF a ha 1 le_rfl (by omega), hkF a ha 2 (by omega) (by omega), hkF a ha 3 (by omega) le_rfl]
  split_ifs <;> rfl

theorem getD_Bl (hkI : ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → kI (trn a k) = !TY ((a + k) % 7)) {b pos : ℕ} (hb : b < 7)
    (hpos : pos < lenB nT b) : (Bl p nT kI cI b).getD pos (dE p) = den p (!TY b) (cBt nT cI b pos) := by
  unfold Bl IL lst
  rw [getD_app3 _ hpos]
  have hs : ∀ k, src b k < 7 := fun k => by unfold src; omega
  unfold cBt
  rw [hkI _ (hs 1) 1 le_rfl (by omega), hkI _ (hs 2) 2 (by omega) (by omega), hkI _ (hs 3) 3 (by omega) le_rfl,
    add_src hb (by omega), add_src hb (by omega), add_src hb (by omega)]
  split_ifs <;> rfl

theorem getD_offA {a k r : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) (hr : r < nT (trn a k)) :
    (Al p nT kF cF a).getD (offA nT a k + r) (dE p) = den p (kF (trn a k)) (cF (trn a k) r) := by
  unfold Al FL lst offA
  rw [getD_app3 _ (by rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl <;> simp <;> omega)]
  rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl
  · simp [hr]
  · simp only [show (2 : ℕ) ≠ 1 by omega, ite_false, ite_true, show ¬ nT (trn a 1) + r < nT (trn a 1) by omega,
      show nT (trn a 1) + r < nT (trn a 1) + nT (trn a 2) by omega, Nat.add_sub_cancel_left]
  · simp only [show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega, ite_false,
      show ¬ nT (trn a 1) + nT (trn a 2) + r < nT (trn a 1) by omega,
      show ¬ nT (trn a 1) + nT (trn a 2) + r < nT (trn a 1) + nT (trn a 2) by omega]
    congr 2; omega

theorem getD_offB {b k r : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) (hr : r < nT (trn (src b k) k)) :
    (Bl p nT kI cI b).getD (offB nT b k + r) (dE p) = den p (kI (trn (src b k) k)) (cI (trn (src b k) k) r) := by
  unfold Bl IL lst offB
  rw [getD_app3 _ (by rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl <;> simp <;> omega)]
  rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl
  · simp [hr]
  · simp only [show (2 : ℕ) ≠ 1 by omega, ite_false, ite_true, show ¬ nT (trn (src b 1) 1) + r < nT (trn (src b 1) 1) by omega,
      show nT (trn (src b 1) 1) + r < nT (trn (src b 1) 1) + nT (trn (src b 2) 2) by omega, Nat.add_sub_cancel_left]
  · simp only [show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega, ite_false,
      show ¬ nT (trn (src b 1) 1) + nT (trn (src b 2) 2) + r < nT (trn (src b 1) 1) by omega,
      show ¬ nT (trn (src b 1) 1) + nT (trn (src b 2) 2) + r < nT (trn (src b 1) 1) + nT (trn (src b 2) 2) by omega]
    congr 2; omega

end Pos

/-! ## Hubs of the pairs -/

/-- The hubs of element `r` of the friendly transition `a → a + k`, if it has a partner: the point-side hub
`hu` holds its `B`-slot at level `a + k`, and its slot at level `a` is incident with the partner (coefficients
`au, bu`); the line-side hub `hv` holds its `A`-slot at level `a`, and its slot at level `a + k` is incident with the
partner (`av, bv`). -/
def hubChk (p : ℕ) (TY : ℕ → Bool) (nT : ℕ → ℕ) (cF cI : ℕ → ℕ → ℕ × ℕ) (pr : ℕ → ℕ → ℕ) (KB KA : ℕ)
    (tA tB hu hv au bu av bv : ℕ → ℕ → ℕ) (a k r : ℕ) : Bool :=
  Nat.beq (pr (trn a k) r) r ||
  (Nat.blt (hu (trn a k) r) KA && Nat.beq (tB (hu (trn a k) r) ((a + k) % 7)) (offB nT ((a + k) % 7) k + r) &&
    adjC p (!TY a) (cBt nT cI a (tB (hu (trn a k) r) a)) (cF (trn a k) (pr (trn a k) r)) (au (trn a k) r)
      (bu (trn a k) r) &&
    Nat.blt (hv (trn a k) r) KB && Nat.beq (tA (hv (trn a k) r) a) (offA nT a k + r) &&
    adjC p (TY ((a + k) % 7)) (cAt nT cF ((a + k) % 7) (tA (hv (trn a k) r) ((a + k) % 7)))
      (cF (trn a k) (pr (trn a k) r)) (av (trn a k) r) (bv (trn a k) r))

theorem getD_lst {n : ℕ} {b : Bool} {cd : ℕ → ℕ × ℕ} {r : ℕ} (hr : r < n) :
    (lst p n b cd).getD r (dE p) = den p b (cd r) := by
  unfold lst; rw [List.getD_eq_getElem _ _ (by simpa using hr)]; simp

theorem hh_of {TY : ℕ → Bool} {nT : ℕ → ℕ} {kF kI : ℕ → Bool} {cF cI : ℕ → ℕ → ℕ × ℕ} {pr : ℕ → ℕ → ℕ}
    {KB KA : ℕ} {tA tB hu hv au bu av bv : ℕ → ℕ → ℕ}
    (hkF : ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → kF (trn a k) = TY a)
    (hkI : ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → kI (trn a k) = !TY ((a + k) % 7))
    (hfr : ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → TY a ≠ TY ((a + k) % 7) → IL p nT kI cI (trn a k) = FL p nT kF cF (trn a k))
    (hcF : ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → ∀ t < nT (trn a k), CodeOK p (TY a) (cF (trn a k) t))
    (hcA : ∀ a < 7, ∀ pos < lenA nT a, CodeOK p (TY a) (cAt nT cF a pos))
    (hcB : ∀ b < 7, ∀ pos < lenB nT b, CodeOK p (!TY b) (cBt nT cI b pos))
    (hprl : ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → ∀ r < nT (trn a k), pr (trn a k) r < nT (trn a k))
    (htA : ∀ a < 7, ∀ v < KB, tA v a < lenA nT a) (htB : ∀ a < 7, ∀ u < KA, tB u a < lenB nT a)
    (hc : ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → TY a ≠ TY ((a + k) % 7) → ∀ r < nT (trn a k),
      hubChk p TY nT cF cI pr KB KA tA tB hu hv au bu av bv a k r = true) :
    ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → TY a ≠ TY ((a + k) % 7) → ∀ r < nT (trn a k), pr (trn a k) r ≠ r →
      (∃ u < KA, (Bl p nT kI cI ((a + k) % 7)).getD (tB u ((a + k) % 7)) (dE p) = den p (kF (trn a k)) (cF (trn a k) r) ∧
        (Hexagon.incGraph hexInc).Adj ((Bl p nT kI cI a).getD (tB u a) (dE p))
          (den p (kF (trn a k)) (cF (trn a k) (pr (trn a k) r)))) ∧
      (∃ v < KB, (Al p nT kF cF a).getD (tA v a) (dE p) = den p (kF (trn a k)) (cF (trn a k) r) ∧
        (Hexagon.incGraph hexInc).Adj ((Al p nT kF cF ((a + k) % 7)).getD (tA v ((a + k) % 7)) (dE p))
          (den p (kF (trn a k)) (cF (trn a k) (pr (trn a k) r)))) := by
  intro a ha k hk1 hk3 hf r hr hne
  have h := hc a ha k hk1 hk3 hf r hr
  have hne' : Nat.beq (pr (trn a k) r) r = false := by
    cases e : Nat.beq (pr (trn a k) r) r
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hne
  simp only [hubChk, hne', Bool.false_or, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨hu1, hu2⟩, hu3⟩, hv1⟩, hv2⟩, hv3⟩ := h
  have ha2 : (a + k) % 7 < 7 := Nat.mod_lt _ (by omega)
  have hpr := hprl a ha k hk1 hk3 r hr
  have hP : CodeOK p (TY a) (cF (trn a k) (pr (trn a k) r)) := hcF a ha k hk1 hk3 _ hpr
  rw [hkF a ha k hk1 hk3]
  refine ⟨⟨hu (trn a k) r, hu1, ?_, ?_⟩, ⟨hv (trn a k) r, hv1, ?_, ?_⟩⟩
  · rw [Nat.eq_of_beq_eq_true hu2]
    have e := getD_offB (p := p) (kI := kI) (cI := cI) (nT := nT) (b := (a + k) % 7) hk1 hk3
      (by rw [src_add ha hk3]; exact hr)
    rw [e, src_add ha hk3]
    have e2 := congrArg (fun l => List.getD l r (dE p)) (hfr a ha k hk1 hk3 hf)
    simp only [IL, FL, getD_lst hr] at e2
    rw [e2, hkF a ha k hk1 hk3]
  · have hpos := htB a ha _ hu1
    rw [getD_Bl hkI ha hpos]
    have := adj_den (b := !TY a) (hcB a ha _ hpos) (by rw [Bool.not_not]; exact hP) hu3
    rwa [Bool.not_not] at this
  · rw [Nat.eq_of_beq_eq_true hv2, getD_offA hk1 hk3 hr, hkF a ha k hk1 hk3]
  · have hpos := htA _ ha2 _ hv1
    rw [getD_Al hkF ha2 hpos]
    have hT : TY a = !TY ((a + k) % 7) := bool_ne hf
    have := adj_den (b := TY ((a + k) % 7)) (hcA _ ha2 _ hpos) (by rw [← hT]; exact hP) hv3
    rwa [← hT] at this

/-! ## The local duality, with its values -/

theorem local_duality' {M m : ℕ} {ptc lnA lnB sg sgi rl : ℕ → ℕ} {rflag : ℕ → Bool} {cert : ℕ → Cert}
    (hG : Glob p M ptc lnA lnB sg sgi) (hR : ∀ v < m, rl v < M ∧ rflag (rl v) = true)
    (hRs : ∀ v, v + 1 < m → rl v < rl (v + 1)) (hC : ∀ v < m, CertSpec p M ptc lnA lnB sg rflag (rl v) (cert v)) :
    ∃ τ : SPt (ZMod p) ≃ HLine (ZMod p), (∀ i < M, τ (Fp p ptc i) = Gl p lnA lnB (sg i)) ∧
      (∀ v < m, ∀ y, Coll hexInc (Fp p ptc (rl v)) y ↔ Conc hexInc (τ (Fp p ptc (rl v))) (τ y)) ∧
      (∀ v < m, ∀ v' < m, ¬ Coll hexInc (Fp p ptc (rl v)) (Fp p ptc (rl v'))) ∧
      (∀ v < m, ∀ v' < m, Fp p ptc (rl v) = Fp p ptc (rl v') → v = v') := by
  letI : Fintype (SPt (ZMod p)) := Fintype.ofFinite _
  letI : Fintype (HLine (ZMod p)) := Fintype.ofFinite _
  have hcL : Fintype.card (HLine (ZMod p)) = Fintype.card (SPt (ZMod p)) := by
    have := card_lines_eq (inc := hexInc (F := ZMod p)) (k := p + 1) (by omega) (fun x => card_lns x)
      (fun W => card_pts W)
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this
  have hgi : ∀ i < M, ∀ j < M, Gl p lnA lnB (sg i) = Gl p lnA lnB (sg j) → i = j := by
    intro i hi j hj h
    have := hG.gl_inj _ (hG.sg i hi).1 _ (hG.sg j hj).1 h
    rw [← (hG.sg i hi).2, ← (hG.sg j hj).2, this]
  obtain ⟨σ, hσ⟩ := exists_equiv_extend hcL.symm (Fp p ptc) (fun i => Gl p lnA lnB (sg i)) hG.fp_inj hgi
  refine ⟨σ, hσ, fun v hv y => ?_, fun v hv v' hv' hcoll => ?_, fun v hv v' hv' h =>
    inj_of_succ hRs v hv v' hv' (hG.fp_inj _ (hR v hv).1 _ (hR v' hv').1 h)⟩
  · have hir := (hR v hv).1
    have hc := hC v hv
    rw [coll_iff hG hir hc, hσ _ hir, conc_iff hG hir hc]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨f, hf, t, ht, hxt⟩ := hc.f4 x hx
      have hxM : x.1 < M := by
        obtain ⟨e, he, hxe⟩ := List.mem_flatMap.1 hx
        exact ((hc.e2 e he).2.2.2 x hxe).1
      exact ⟨f, hf, t, ht, by rw [hσ _ hxM, hxt]⟩
    · rintro ⟨f, hf, t, ht, hyt⟩
      obtain ⟨x, hx, hxt⟩ := hc.f3 f hf t ht
      have hxM : x.1 < M := by
        obtain ⟨e, he, hxe⟩ := List.mem_flatMap.1 hx
        exact ((hc.e2 e he).2.2.2 x hxe).1
      refine ⟨x, hx, σ.injective ?_⟩
      rw [hyt, hσ _ hxM, hxt]
  · have hir := (hR v hv).1
    obtain ⟨x, hx, hxe⟩ := (coll_iff hG hir (hC v hv) _).1 hcoll
    obtain ⟨e, he, hxe'⟩ := List.mem_flatMap.1 hx
    obtain ⟨hxM, -, hfl, -⟩ := ((hC v hv).e2 e he).2.2.2 x hxe'
    have h1 := hG.fp_inj _ (hR v' hv').1 _ hxM hxe
    have h2 := (hR v' hv').2
    rw [h1, hfl] at h2
    exact Bool.false_ne_true h2

/-! ## Codes and duplicates -/

theorem nodup_lst {n : ℕ} {b : Bool} {cd : ℕ → ℕ × ℕ}
    (h : ∀ t < n, ∀ t' < n, den p b (cd t) = den p b (cd t') → t = t') : (lst p n b cd).Nodup :=
  nodup_rmap h

theorem hcA_of {TY : ℕ → Bool} {nT : ℕ → ℕ} {cF : ℕ → ℕ → ℕ × ℕ}
    (hcF : ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → ∀ t < nT (trn a k), CodeOK p (TY a) (cF (trn a k) t)) :
    ∀ a < 7, ∀ pos < lenA nT a, CodeOK p (TY a) (cAt nT cF a pos) := by
  intro a ha pos hpos
  unfold lenA at hpos; unfold cAt
  split_ifs with h1 h2
  · exact hcF a ha 1 le_rfl (by omega) _ h1
  · exact hcF a ha 2 (by omega) (by omega) _ (by omega)
  · exact hcF a ha 3 (by omega) le_rfl _ (by omega)

theorem hcB_of {TY : ℕ → Bool} {nT : ℕ → ℕ} {kI : ℕ → Bool} {cI : ℕ → ℕ → ℕ × ℕ}
    (hkI : ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → kI (trn a k) = !TY ((a + k) % 7))
    (hcI : ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → ∀ t < nT (trn a k), CodeOK p (kI (trn a k)) (cI (trn a k) t)) :
    ∀ b < 7, ∀ pos < lenB nT b, CodeOK p (!TY b) (cBt nT cI b pos) := by
  intro b hb pos hpos
  have hs : ∀ k, src b k < 7 := fun k => by unfold src; omega
  have key : ∀ k, 1 ≤ k → k ≤ 3 → ∀ t < nT (trn (src b k) k), CodeOK p (!TY b) (cI (trn (src b k) k) t) := by
    intro k hk1 hk3 t ht
    have := hcI _ (hs k) k hk1 hk3 t ht
    rwa [hkI _ (hs k) k hk1 hk3, add_src hb hk3] at this
  unfold lenB at hpos; unfold cBt
  split_ifs with h1 h2
  · exact key 1 le_rfl (by omega) _ h1
  · exact key 2 (by omega) (by omega) _ (by omega)
  · exact key 3 (by omega) le_rfl _ (by omega)

/-! ## The transitions of the local duality -/

/-- The freed points of a certificate, by code. -/
def lcP (c : LC) (t : ℕ) : ℕ × ℕ := (c.ptc (c.rl t), 0)

/-- Their lines `σ r`, by basis. -/
def lcL (c : LC) (t : ℕ) : ℕ × ℕ := (c.lnA (c.sg (c.rl t)), c.lnB (c.sg (c.rl t)))

theorem lc_denP {c : LC} (t : ℕ) : den p false (lcP c t) = .inl (Fp p c.ptc (c.rl t)) := rfl

theorem lc_nodupP' {c : LC} (hc : c.Ok p) : (lst p c.m false (lcP c)).Nodup :=
  nodup_lst (fun t ht t' ht' e =>
    inj_of_succ hc.rs t ht t' ht' (hc.glob.fp_inj _ (hc.r t ht).1 _ (hc.r t' ht').1 (Sum.inl_injective e)))

theorem lc_nodupL' {c : LC} (hc : c.Ok p) : (lst p c.m true (lcL c)).Nodup := by
  refine nodup_lst (fun t ht t' ht' e => ?_)
  have e' : Gl p c.lnA c.lnB (c.sg (c.rl t)) = Gl p c.lnA c.lnB (c.sg (c.rl t')) := Sum.inr_injective e
  have s1 := hc.glob.sg _ (hc.r t ht).1
  have s2 := hc.glob.sg _ (hc.r t' ht').1
  have h1 := hc.glob.gl_inj _ s1.1 _ s2.1 e'
  have h2 : c.rl t = c.rl t' := by rw [← s1.2, ← s2.2, h1]
  exact inj_of_succ hc.rs t ht t' ht' h2

section LCfacts

variable {c : LC} (hc : c.Ok p) {τd : SPt (ZMod p) ≃ HLine (ZMod p)}
  (hval : ∀ i < c.M, τd (Fp p c.ptc i) = Gl p c.lnA c.lnB (c.sg i))
  (hdual : ∀ v < c.m, ∀ y, Coll hexInc (Fp p c.ptc (c.rl v)) y ↔ Conc hexInc (τd (Fp p c.ptc (c.rl v))) (τd y))
  (hnc : ∀ v < c.m, ∀ v' < c.m, ¬ Coll hexInc (Fp p c.ptc (c.rl v)) (Fp p c.ptc (c.rl v')))
  (hinj : ∀ v < c.m, ∀ v' < c.m, Fp p c.ptc (c.rl v) = Fp p c.ptc (c.rl v') → v = v')
include hc

include hval in
theorem lc_denL {t : ℕ} (ht : t < c.m) : den p true (lcL c t) = .inr (τd (Fp p c.ptc (c.rl t))) := by
  rw [hval _ (hc.r t ht).1]; rfl

theorem lc_codeP : ∀ t < c.m, CodeOK p false (lcP c t) := fun t ht => hc.glob.pt _ (hc.r t ht).1

theorem lc_codeL : ∀ t < c.m, CodeOK p true (lcL c t) := fun t ht =>
  hc.glob.ln _ (hc.glob.sg _ (hc.r t ht).1).1

include hinj in
theorem lc_nodupP : (lst p c.m false (lcP c)).Nodup :=
  nodup_lst (fun t ht t' ht' e => hinj t ht t' ht' (Sum.inl_injective e))

include hval hinj in
theorem lc_nodupL : (lst p c.m true (lcL c)).Nodup := by
  refine nodup_lst (fun t ht t' ht' e => hinj t ht t' ht' (τd.injective (Sum.inr_injective (α := SPt (ZMod p)) ?_)))
  rw [← lc_denL hc hval ht, ← lc_denL hc hval ht', e]

include hval in
theorem lc_swP : ∀ t < c.m, swapE τd (den p false (lcP c t)) = den p true (lcL c t) := by
  intro t ht; rw [lc_denL hc hval ht]; rfl

include hval in
theorem lc_swL : ∀ t < c.m, swapE τd (den p true (lcL c t)) = den p false (lcP c t) := by
  intro t ht; rw [lc_denL hc hval ht, swapE_inr, Equiv.symm_apply_apply]; rfl

include hdual in
theorem lc_r2P : ∀ t < c.m, ∀ x, Co hexInc (den p false (lcP c t)) x ↔
    Co hexInc (swapE τd (den p false (lcP c t))) (swapE τd x) := by
  intro t ht x
  rw [lc_denP]
  rcases x with y | l
  · rw [swapE_inl, swapE_inl, co_inl, co_inr]; exact hdual t ht y
  · rw [swapE_inl, swapE_inr]
    exact iff_of_false not_co_inl_inr not_co_inr_inl

include hval hdual in
theorem lc_r2L : ∀ t < c.m, ∀ x, Co hexInc (den p true (lcL c t)) x ↔
    Co hexInc (swapE τd (den p true (lcL c t))) (swapE τd x) := by
  intro t ht x
  rw [lc_denL hc hval ht]
  rcases x with y | l
  · rw [swapE_inr, swapE_inl]
    exact iff_of_false not_co_inr_inl not_co_inl_inr
  · rw [swapE_inr, swapE_inr, co_inr, co_inl, Equiv.symm_apply_apply]
    have := hdual t ht (τd.symm l)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm

include hnc in
theorem lc_prP : ∀ r < c.m, ∀ s < c.m, Co hexInc (den p false (lcP c r)) (den p false (lcP c s)) → s = r := by
  intro r hr s hs h
  rw [lc_denP, lc_denP, co_inl] at h
  exact absurd h (hnc r hr s hs)

include hval hdual hnc in
theorem lc_prL : ∀ r < c.m, ∀ s < c.m, Co hexInc (den p true (lcL c r)) (den p true (lcL c s)) → s = r := by
  intro r hr s hs h
  rw [lc_denL hc hval hr, lc_denL hc hval hs, co_inr] at h
  exact absurd ((hdual r hr _).2 h) (hnc r hr s hs)

end LCfacts

/-! ## Small facts for the records -/

theorem nbChk_spec {KO D : ℕ} {nbX nbY : ℕ → List ℕ} {x : ℕ}
    (h : (allP (fun y => Nat.blt y KO && (nbY y).contains x) (nbX x) && Nat.ble (lenP (nbX x)) D) = true) :
    (∀ y ∈ nbX x, y < KO ∧ x ∈ nbY y) ∧ (nbX x).length ≤ D := by
  simp only [Bool.and_eq_true, allP_eq, List.all_eq_true, Nat.blt_eq, Nat.ble_eq, lenP_eq,
    List.contains_iff_mem] at h
  exact ⟨fun y hy => h.1 y hy, h.2⟩

theorem hubChk_of_pr {TY : ℕ → Bool} {nT : ℕ → ℕ} {cF cI : ℕ → ℕ → ℕ × ℕ} {pr : ℕ → ℕ → ℕ} {KB KA : ℕ}
    {tA tB hu hv au bu av bv : ℕ → ℕ → ℕ} {a k r : ℕ} (h : pr (trn a k) r = r) :
    hubChk p TY nT cF cI pr KB KA tA tB hu hv au bu av bv a k r = true := by
  simp [hubChk, h]

/-- Facts about transitions, one transition number at a time. -/
theorem by_tr {P : ℕ → ℕ → Prop} (h : ∀ tr < 21, P (tr / 3) (tr % 3 + 1)) :
    ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → P a k := by
  intro a ha k hk1 hk3
  have := h (trn a k) (by unfold trn; omega)
  have e1 : trn a k / 3 = a := by unfold trn; omega
  have e2 : trn a k % 3 + 1 = k := by unfold trn; omega
  rwa [e1, e2] at this

end BipartiteDD.LeanAll.Relax7
