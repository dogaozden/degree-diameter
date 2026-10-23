import BipartiteDD.Haar.D7D9b.Gens

/-! Raw arithmetic for the (7,9) record on `PSL(2, 29) × Z_19`.

The stage checks of `D7D9b.Check` run on naturals: a matrix is four naturals below `29` (its entries mod `29`),
and the `Z_19` coordinate is a natural below `19`. Kernel evaluation of these operations is much faster than
the `ZMod` operations of `PSL29`. This file proves that the raw computation is the group computation:

* `valsP`, `valsG` give the entries of a group element; `valsP_mul`, `valsP_inv`, `valsG_mul`, `valsG_inv` say that
  the raw operations `rmul`/`rinv`, followed by the sign normalisation `rcanon`, compute the group product;
* `valsG_wordA`, `valsG_wordB`: the raw words `rwA c`, `rwB c` compute the group words `wordA c`, `wordB c`;
* `idxG_wordA`, `idxG_wordB`: the index of a word is `encRaw` of its raw value.

The raw entries are the canonical representatives of `PSL29`, so `encRaw` is `PSL29.enc` on them. -/

namespace BipartiteDD.Haar.D7D9b

open BipartiteDD.Haar.PSL29

/-! ### Raw arithmetic -/

/-- A raw matrix: the four entries, as naturals below `29`. -/
abbrev RM := ℕ × ℕ × ℕ × ℕ

/-- The raw product of two matrices, entries reduced mod `29`; the sign is not normalised. -/
def rmul (x y : RM) : RM :=
  ((x.1 * y.1 + x.2.1 * y.2.2.1) % 29, (x.1 * y.2.1 + x.2.1 * y.2.2.2) % 29,
    (x.2.2.1 * y.1 + x.2.2.2 * y.2.2.1) % 29, (x.2.2.1 * y.2.1 + x.2.2.2 * y.2.2.2) % 29)

/-- The raw inverse of a determinant-one matrix `[[a, b], [c, d]]`, namely `[[d, -b], [-c, a]]`. -/
def rinv (x : RM) : RM := (x.2.2.2, (29 - x.2.1) % 29, (29 - x.2.2.1) % 29, x.1)

/-- The sign test of `PSL29.posB`, on naturals `a` (first entry) and `c` (third entry). -/
def posN2 (a c : ℕ) : Bool := if c = 0 then decide (a ≤ 14) else decide (c ≤ 14)

/-- The representative of the sign class of `x`: `x` itself when `posN2` holds, else its negative. -/
def rcanon (x : RM) : RM :=
  if posN2 x.1 x.2.2.1 then x
  else ((29 - x.1) % 29, (29 - x.2.1) % 29, (29 - x.2.2.1) % 29, (29 - x.2.2.2) % 29)

/-- The index of a canonical raw matrix: `PSL29.enc` on its entries. -/
def encRaw (x : RM) : ℕ :=
  if x.2.2.1 = 0 then (x.1 - 1) * 29 + x.2.1 else 406 + ((x.2.2.1 - 1) * 29 + x.1) * 29 + x.2.2.2

/-- The raw element of `PSL29 × Z_19`: a matrix and a `Z_19` coordinate. -/
def rmz (x y : RM × ℕ) : RM × ℕ := (rcanon (rmul x.1 y.1), (x.2 + y.2) % 19)

/-- The raw inverse, in `PSL29 × Z_19`. -/
def izc (x : RM × ℕ) : RM × ℕ := (rcanon (rinv x.1), (19 - x.2) % 19)

/-! ### The words -/

/-- The digit `k` of the code `c`, in base 7. -/
def digit (c k : ℕ) : ℕ := c / 7 ^ k % 7

theorem digit_lt (c k : ℕ) : digit c k < 7 := Nat.mod_lt _ (by norm_num)

/-- The raw values of the generators `sel j`, `j < 7`. -/
def rsel : List (RM × ℕ) :=
  [((1, 0, 0, 1), 0), ((6, 23, 9, 25), 18), ((20, 5, 9, 11), 12), ((20, 23, 7, 11), 8),
    ((21, 24, 7, 26), 17), ((12, 23, 7, 28), 5), ((23, 24, 9, 17), 16)]

/-- The raw value of `sel j`. -/
def rs (j : ℕ) : RM × ℕ := rsel.getD j ((1, 0, 0, 1), 0)

/-- The A-word of the code `c`, raw: `x0⁻¹ x1 x2⁻¹ x3 x4⁻¹ x5 x6⁻¹ x7`, multiplied left to right. -/
def rwA (c : ℕ) : RM × ℕ :=
  rmz (rmz (rmz (rmz (rmz (rmz (rmz (izc (rs (digit c 0))) (rs (digit c 1))) (izc (rs (digit c 2))))
    (rs (digit c 3))) (izc (rs (digit c 4)))) (rs (digit c 5))) (izc (rs (digit c 6)))) (rs (digit c 7))

/-- The B-word of the code `c`, raw: `x0 x1⁻¹ x2 x3⁻¹ x4 x5⁻¹ x6 x7⁻¹`, multiplied left to right. -/
def rwB (c : ℕ) : RM × ℕ :=
  rmz (rmz (rmz (rmz (rmz (rmz (rmz (rs (digit c 0)) (izc (rs (digit c 1)))) (rs (digit c 2)))
    (izc (rs (digit c 3)))) (rs (digit c 4))) (izc (rs (digit c 5)))) (rs (digit c 6))) (izc (rs (digit c 7)))

/-- The A-word of the code `c` in `G`. -/
def wordA (c : ℕ) : G :=
  (sel (digit c 0))⁻¹ * sel (digit c 1) * (sel (digit c 2))⁻¹ * sel (digit c 3) *
    (sel (digit c 4))⁻¹ * sel (digit c 5) * (sel (digit c 6))⁻¹ * sel (digit c 7)

/-- The B-word of the code `c` in `G`. -/
def wordB (c : ℕ) : G :=
  sel (digit c 0) * (sel (digit c 1))⁻¹ * sel (digit c 2) * (sel (digit c 3))⁻¹ *
    sel (digit c 4) * (sel (digit c 5))⁻¹ * sel (digit c 6) * (sel (digit c 7))⁻¹

/-! ### Group elements as raw values -/

/-- The entries of a `PSL29` element, as naturals. -/
def valsP (g : Grp) : RM := (g.a.val, g.b.val, g.c.val, g.d.val)

/-- The raw value of an element of `G`. -/
def valsG (g : G) : RM × ℕ := (valsP g.1, (Multiplicative.toAdd g.2).val)

theorem zero_iff_of_lt {c : ℕ} (hc : c < 29) : (c : ZMod 29) = 0 ↔ c = 0 := by
  rw [← ZMod.val_eq_zero, ZMod.val_natCast, Nat.mod_eq_of_lt hc]

theorem posB_natCast {a c : ℕ} (ha : a < 29) (hc : c < 29) :
    posB (a : ZMod 29) (c : ZMod 29) = posN2 a c := by
  unfold posB posN2
  simp only [zero_iff_of_lt hc, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc]

theorem val_neg_eq (n : ℕ) [NeZero n] (z : ZMod n) : (-z).val = (n - z.val) % n := by
  rw [ZMod.neg_val]
  split_ifs with h
  · subst h
    simp
  · have h1 : z.val ≠ 0 := fun e => h ((ZMod.val_eq_zero z).1 e)
    have h2 := ZMod.val_lt z
    rw [Nat.mod_eq_of_lt (by omega)]

theorem val_neg_natCast {x : ℕ} (hx : x < 29) : (-(x : ZMod 29)).val = (29 - x) % 29 := by
  rw [val_neg_eq 29, ZMod.val_natCast, Nat.mod_eq_of_lt hx]

/-- A raw matrix with entries below `29` and determinant `1`, whose cast is `canon a b c d`, is the value of
`canon a b c d`. -/
theorem valsP_canon (a b c d : ZMod 29) (h : a * d - b * c = 1) (r : RM)
    (hr : r.1 < 29 ∧ r.2.1 < 29 ∧ r.2.2.1 < 29 ∧ r.2.2.2 < 29)
    (ha : (r.1 : ZMod 29) = a) (hb : (r.2.1 : ZMod 29) = b) (hc : (r.2.2.1 : ZMod 29) = c)
    (hd : (r.2.2.2 : ZMod 29) = d) :
    valsP (canon a b c d h) = rcanon r := by
  obtain ⟨r1, r2, r3, r4⟩ := r
  obtain ⟨h1, h2, h3, h4⟩ := hr
  simp only at h1 h2 h3 h4 ha hb hc hd
  subst ha hb hc hd
  unfold canon
  by_cases hp : posB (r1 : ZMod 29) (r3 : ZMod 29) = true
  · rw [dif_pos hp]
    have hn : posN2 r1 r3 = true := by
      rw [← posB_natCast h1 h3]
      exact hp
    simp only [valsP, rcanon, hn, if_true, ZMod.val_natCast, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
      Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4]
  · rw [dif_neg hp]
    have hn : posN2 r1 r3 = false := by
      rw [← posB_natCast h1 h3]
      simpa using hp
    simp [valsP, rcanon, hn, val_neg_natCast h1, val_neg_natCast h2, val_neg_natCast h3, val_neg_natCast h4]

theorem valsP_mul (x y : Grp) : valsP (x * y) = rcanon (rmul (valsP x) (valsP y)) := by
  rw [mul_def]
  refine valsP_canon _ _ _ _ _ (rmul (valsP x) (valsP y)) ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_
  · exact Nat.mod_lt _ (by norm_num)
  · exact Nat.mod_lt _ (by norm_num)
  · exact Nat.mod_lt _ (by norm_num)
  · exact Nat.mod_lt _ (by norm_num)
  · simp only [rmul, valsP, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  · simp only [rmul, valsP, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  · simp only [rmul, valsP, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  · simp only [rmul, valsP, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]

theorem valsP_inv (x : Grp) : valsP x⁻¹ = rcanon (rinv (valsP x)) := by
  rw [inv_def]
  refine valsP_canon _ _ _ _ _ (rinv (valsP x)) ⟨?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_
  · exact ZMod.val_lt x.d
  · exact Nat.mod_lt _ (by norm_num)
  · exact Nat.mod_lt _ (by norm_num)
  · exact ZMod.val_lt x.a
  · simp [rinv, valsP]
  · simp only [rinv, valsP]
    rw [ZMod.natCast_mod, Nat.cast_sub (ZMod.val_lt x.b).le, ZMod.natCast_self, ZMod.natCast_zmod_val, zero_sub]
  · simp only [rinv, valsP]
    rw [ZMod.natCast_mod, Nat.cast_sub (ZMod.val_lt x.c).le, ZMod.natCast_self, ZMod.natCast_zmod_val, zero_sub]
  · simp [rinv, valsP]

theorem valsG_mul (x y : G) : valsG (x * y) = rmz (valsG x) (valsG y) := by
  have hm : (Multiplicative.toAdd (x.2 * y.2)).val =
      ((Multiplicative.toAdd x.2).val + (Multiplicative.toAdd y.2).val) % 19 :=
    ZMod.val_add _ _
  simp only [valsG, rmz, valsP_mul, Prod.fst_mul, Prod.snd_mul, hm]

theorem valsG_inv (x : G) : valsG x⁻¹ = izc (valsG x) := by
  have hi : (Multiplicative.toAdd x.2⁻¹).val = (19 - (Multiplicative.toAdd x.2).val) % 19 :=
    val_neg_eq 19 _
  simp only [valsG, izc, valsP_inv, Prod.fst_inv, Prod.snd_inv, hi]

/-- The raw values of the generators. -/
theorem valsG_sel_all : ∀ j < 7, valsG (sel j) = rs j := by
  decide +kernel

theorem valsG_sel (c k : ℕ) : valsG (sel (digit c k)) = rs (digit c k) :=
  valsG_sel_all _ (digit_lt c k)

theorem valsG_wordA (c : ℕ) : valsG (wordA c) = rwA c := by
  simp only [wordA, rwA, valsG_mul, valsG_inv, valsG_sel]

theorem valsG_wordB (c : ℕ) : valsG (wordB c) = rwB c := by
  simp only [wordB, rwB, valsG_mul, valsG_inv, valsG_sel]

/-! ### Indices -/

theorem enc_eq_encRaw (x : Grp) : enc x.a x.b x.c x.d = encRaw (valsP x) := by
  unfold enc encRaw valsP
  simp only [ZMod.val_eq_zero]

theorem idxG_eq (g : G) : idxG g = encRaw (valsG g).1 * 19 + (valsG g).2 := by
  unfold idxG valsG
  rw [enc_eq_encRaw]

theorem idxG_wordA (c : ℕ) : idxG (wordA c) = encRaw (rwA c).1 * 19 + (rwA c).2 := by
  rw [idxG_eq, valsG_wordA]

theorem idxG_wordB (c : ℕ) : idxG (wordB c) = encRaw (rwB c).1 * 19 + (rwB c).2 := by
  rw [idxG_eq, valsG_wordB]

end BipartiteDD.Haar.D7D9b
