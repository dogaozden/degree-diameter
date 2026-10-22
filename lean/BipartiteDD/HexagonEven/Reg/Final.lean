import BipartiteDD.HexagonEven.Reg.Choice
import BipartiteDD.Regular.TheoremR

/-! Theorem R instance, part 4: the regular graph of diameter 6.

Apply `Regular.regular_of_twin_classes` to the bipartite graph of `levRel` with the deleted set
`delSet v W m (Ldel d Q)` (`Choice`). The hypotheses are: the twin condition (`levRel_twin`), the size of the
deleted set (`card_delSet_eq`), the class condition (`hclass`), the degree bounds (`levRel_isBipartiteDegDiam`,
`ncard_degR_ge`, `ncard_degL_restrict_ge`), and the deficit bound: the total deficit of the point side is at least
the number of deleted edges, which is at least `(q + 1) |S|` (`degL_restrictR_add` and double counting). -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonEven

open BipartiteDD.HexagonD

open BipartiteDD.Hexagon BipartiteDD.Doubling BipartiteDD.Regular Finset
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] {d : F}

/-- The numerical bound of the completion lemma: `2 s (Δ + s + 1) < |S| (q + 1)` with `s = m - 1`, `Δ = q + m`. -/
theorem numeric_bound {q m : ℕ} (hq : 2 ≤ q) (hm : 2 ≤ m) :
    2 * (m - 1) * (q + m + (m - 1) + 1) < (m - 1) * m * (q ^ 3 - q + m) * (q + 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 2 := ⟨m - 2, by omega⟩
  have hT : q + 6 ≤ q ^ 3 := by
    have h4 : 4 ≤ q ^ 2 := by nlinarith
    have h5 : q ^ 3 = q * q ^ 2 := by ring
    rw [h5]
    nlinarith
  obtain ⟨T, hT'⟩ : ∃ T, q ^ 3 - q = T + 6 := ⟨q ^ 3 - q - 6, by omega⟩
  have e : a + 2 - 1 = a + 1 := by omega
  rw [hT', e]
  nlinarith [Nat.zero_le (a * q), Nat.zero_le (a * T), Nat.zero_le (T * q), Nat.zero_le (a * a)]

theorem regular_levRel [Fintype (SPt F)] [Fintype (HLine F)] {m : ℕ} (hm2 : 2 ≤ m) (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (hchar : (2 : F) = 0)
    (v : SLineE d) {W : Set (HLine F)} (hW : Whiskers d v W)
    (hWc : W.ncard + Fintype.card F ^ 2 = Fintype.card F ^ 4) :
    ∃ G : SimpleGraph (Fin (2 * Fintype.card (PtVer d v.1 W m))),
      IsBipartiteRegDiam G (Fintype.card F + m) 6 := by
  have hm : 0 < m := by omega
  obtain ⟨Q, hQ, hQcard⟩ := exists_Q v hd hchar
  have hdeg := levRel_isBipartiteDegDiam hd hchar hm v hW
  have hdegL : ∀ a : PtVer d v.1 W m, degL (levRel d v.1 W m) a ≤ Fintype.card F + m := fun a => by
    unfold degL
    rw [← BipartiteDD.Regular.ncard_neighborSet_inl]
    exact hdeg.2.1 _
  have hdegR : ∀ b : LnVer d v.1 W m, degR (levRel d v.1 W m) b ≤ Fintype.card F + m := fun b => by
    unfold degR
    rw [← BipartiteDD.Regular.ncard_neighborSet_inr]
    exact hdeg.2.1 _
  have hSdel : ∀ x ∈ delSet v W m (Ldel d Q), Dele d v.1 W m x := fun x hx => (mem_filter.1 hx).2.1
  have hSmem : ∀ x : LnVer d v.1 W m, x ∈ (delSet v W m (Ldel d Q) : Set (LnVer d v.1 W m)) →
      Dele d v.1 W m x :=
    fun x hx => hSdel x (mem_coe.1 hx)
  have hScard := card_delSet_eq v W hd hchar hm Q hQ hQcard
  -- The side sizes: `|β| = |α| + |S|`.
  have hS : Fintype.card (PtVer d v.1 W m) + (delSet v W m (Ldel d Q)).card =
      Fintype.card (LnVer d v.1 W m) := by
    have h := (natCard_sides hd hchar hm v hW hWc).2
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
    have hq : Fintype.card F ≤ Fintype.card F ^ 3 := Nat.le_self_pow (by norm_num) _
    rw [hScard]
    have e : Fintype.card F ^ 3 - Fintype.card F + m + Fintype.card F = Fintype.card F ^ 3 + m := by
      omega
    have e2 : (m - 1) * m * (Fintype.card F ^ 3 - Fintype.card F + m) + (m - 1) * m * Fintype.card F =
        (m - 1) * m * (Fintype.card F ^ 3 + m) := by
      rw [← mul_add, e]
    omega
  have hclass' := hclass v W hm (Ldel d Q)
  have hsα : ∀ a : PtVer d v.1 W m,
      Fintype.card F + m - degL (restrictR (levRel d v.1 W m) (delSet v W m (Ldel d Q) : Set _)) a ≤ m - 1 := by
    rintro ⟨p, s⟩
    have h := ncard_degL_restrict_ge v W hd hchar hm (delSet v W m (Ldel d Q) : Set _) hSmem p s
    have h' : degL (restrictR (levRel d v.1 W m) (delSet v W m (Ldel d Q) : Set _)) ⟨p, s⟩ =
        {b : {b : LnVer d v.1 W m // b ∉ (delSet v W m (Ldel d Q) : Set _)} |
          levRel d v.1 W m ⟨p, s⟩ b.1}.ncard := rfl
    rw [h']
    omega
  have hsβ : ∀ b : {b : LnVer d v.1 W m // b ∉ (delSet v W m (Ldel d Q) : Set _)},
      Fintype.card F + m - degR (restrictR (levRel d v.1 W m) (delSet v W m (Ldel d Q) : Set _)) b ≤ m - 1 := by
    intro b
    obtain ⟨⟨l, t⟩, hb⟩ := b
    have h := ncard_degR_ge v W hm l t
    have h' : degR (restrictR (levRel d v.1 W m) (delSet v W m (Ldel d Q) : Set _)) ⟨⟨l, t⟩, hb⟩ =
        {a : PtVer d v.1 W m | levRel d v.1 W m a ⟨l, t⟩}.ncard := rfl
    rw [h']
    omega
  -- Deficit bound: the point side loses at least `|S|` edges to `S`, and each deleted version has `q + 1`
  -- neighbours.
  have hsum1 : ∑ a : PtVer d v.1 W m, ((delSet v W m (Ldel d Q)).filter fun b => levRel d v.1 W m a b).card ≤
      ∑ a : PtVer d v.1 W m, (Fintype.card F + m - degL (restrictR (levRel d v.1 W m)
        (delSet v W m (Ldel d Q) : Set _)) a) := by
    refine Finset.sum_le_sum fun a _ => ?_
    have h1 := degL_restrictR_add (levRel d v.1 W m) (delSet v W m (Ldel d Q)) a
    have h2 := hdegL a
    omega
  have hsum2 : ∑ a : PtVer d v.1 W m, ((delSet v W m (Ldel d Q)).filter fun b => levRel d v.1 W m a b).card =
      ∑ b ∈ delSet v W m (Ldel d Q), degR (levRel d v.1 W m) b := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold degR
    rw [ncard_setOf_eq_card_filter, Finset.card_filter]
  have hsum3 : (delSet v W m (Ldel d Q)).card * (Fintype.card F + 1) ≤
      ∑ b ∈ delSet v W m (Ldel d Q), degR (levRel d v.1 W m) b := by
    have := Finset.card_nsmul_le_sum (delSet v W m (Ldel d Q)) (fun b => degR (levRel d v.1 W m) b)
      (Fintype.card F + 1) (fun b _ => by
        obtain ⟨l, t⟩ := b
        exact ncard_degR_ge v W hm l t)
    simpa [smul_eq_mul] using this
  have hbig : 2 * (m - 1) * (Fintype.card F + m + (m - 1) + 1) <
      ∑ a : PtVer d v.1 W m, (Fintype.card F + m - degL (restrictR (levRel d v.1 W m)
        (delSet v W m (Ldel d Q) : Set _)) a) := by
    have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
    have hnum : 2 * (m - 1) * (Fintype.card F + m + (m - 1) + 1) <
        (delSet v W m (Ldel d Q)).card * (Fintype.card F + 1) := by
      rw [hScard]
      exact numeric_bound hq2 hm2
    exact lt_of_lt_of_le hnum (hsum3.trans (hsum2.symm.le.trans hsum1))
  exact regular_of_twin_classes (levRel d v.1 W m) (cls v W)
    (fun b b' h a => levRel_twin hd hchar v b b' (congrArg Subtype.val h) a)
    (Fintype.card F + m) (m - 1) 6 (delSet v W m (Ldel d Q)) hS (fun k => hclass' k)
    (fun a => hdegL a) (fun b => hdegR b) hsα hsβ hbig hdeg.2.2

section Final

/-- **Theorem R (brief step 4).** For odd `q` and `m ≥ 2` there is a `(q + m)`-regular bipartite graph of diameter
at most `6` on `2 (q+1) (q⁴ + q² + 1 + (m - 1)(q³ + m + 1))` vertices. -/
theorem theoremR {m : ℕ} (hm2 : 2 ≤ m) (hchar : (2 : F) = 0) (hq : 4 ≤ Fintype.card F) :
    ∃ G : SimpleGraph (Fin (2 * (Fintype.card F + 1) * (Fintype.card F ^ 4 + Fintype.card F ^ 2 + 1 +
        (m - 1) * (Fintype.card F ^ 3 + m + 1)))),
      IsBipartiteRegDiam G (Fintype.card F + m) 6 := by
  obtain ⟨d, c0, c1, hd, -, hW, hcard, -⟩ := theorem4_even (F := F) hchar hq
  haveI : Fintype (SPt F) := Fintype.ofFinite _
  haveI : Fintype (HLine F) := by
    have := finite_hline_even (F := F)
    exact Fintype.ofFinite _
  obtain ⟨G, hG⟩ := regular_levRel hm2 hd hchar (vS' d) hW hcard
  have hcardP : Fintype.card (PtVer d (vS' d).1 (Wset d c0 c1) m) =
      (Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4) +
        (m - 1) * ((Fintype.card F ^ 3 + 1) * (Fintype.card F + 1) + m * (Fintype.card F + 1)) := by
    rw [← Nat.card_eq_fintype_card]
    exact (natCard_sides hd hchar (by omega) (vS' d) hW hcard).1
  have hfin : 2 * Fintype.card (PtVer d (vS' d).1 (Wset d c0 c1) m) =
      2 * (Fintype.card F + 1) * (Fintype.card F ^ 4 + Fintype.card F ^ 2 + 1 +
        (m - 1) * (Fintype.card F ^ 3 + m + 1)) := by
    rw [hcardP]
    generalize m - 1 = k
    ring
  exact ⟨G.comap (finCongr hfin).symm, hG.comap (finCongr hfin)⟩

/-- **Theorem R, `m = 2`.** For odd `q` there is a `(q + 2)`-regular bipartite graph of diameter at most `6` on
`2 (q+1) (q⁴ + q³ + q² + 4)` vertices. -/
theorem theoremR_two (hchar : (2 : F) = 0) (hq : 4 ≤ Fintype.card F) :
    ∃ G : SimpleGraph (Fin (2 * (Fintype.card F + 1) *
        (Fintype.card F ^ 4 + Fintype.card F ^ 3 + Fintype.card F ^ 2 + 4))),
      IsBipartiteRegDiam G (Fintype.card F + 2) 6 := by
  obtain ⟨G, hG⟩ := theoremR (F := F) (m := 2) le_rfl hchar hq
  have e : 2 * (Fintype.card F + 1) * (Fintype.card F ^ 4 + Fintype.card F ^ 2 + 1 +
      (2 - 1) * (Fintype.card F ^ 3 + 2 + 1)) =
      2 * (Fintype.card F + 1) * (Fintype.card F ^ 4 + Fintype.card F ^ 3 + Fintype.card F ^ 2 + 4) := by
    rw [show (2 : ℕ) - 1 = 1 from rfl]
    ring
  exact ⟨G.comap (finCongr e).symm, hG.comap (finCongr e)⟩

end Final

end BipartiteDD.HexagonEven
