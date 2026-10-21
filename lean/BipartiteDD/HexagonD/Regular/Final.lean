import BipartiteDD.HexagonD.Regular.Choice
import BipartiteDD.Regular.TheoremR

/-! Theorem R instance, part 4: the regular graph of diameter 6.

Apply `Regular.regular_of_twin_classes` to the bipartite graph of `levRel` with the deleted set
`delSet v W m (Ldel c Q)` (`Choice`). The hypotheses are: the twin condition (`levRel_twin`), the size of the
deleted set (`card_delSet_eq`), the class condition (`hclass`), the degree bounds (`levRel_isBipartiteDegDiam`,
`ncard_degR_ge`, `ncard_degL_restrict_ge`), and the deficit bound: the total deficit of the point side is at least
the number of deleted edges, which is at least `(q + 1) |S|` (`degL_restrictR_add` and double counting). -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon BipartiteDD.Doubling BipartiteDD.Regular Finset
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)] {c : F}

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

theorem regular_levRel [Fintype (SPt F)] [Fintype (HLine F)] {m : ℕ} (hm2 : 2 ≤ m) (hc : ¬ IsSquare (-c))
    (v : SLine c) {W : Set (HLine F)} (hW : Whiskers c v W)
    (hWc : W.ncard + Fintype.card F ^ 2 = Fintype.card F ^ 4) :
    ∃ G : SimpleGraph (Fin (2 * Fintype.card (PtVer c v.1 W m))),
      IsBipartiteRegDiam G (Fintype.card F + m) 6 := by
  have hm : 0 < m := by omega
  obtain ⟨Q, hQ, hQcard⟩ := exists_Q v hc
  have hdeg := levRel_isBipartiteDegDiam hc hm v hW
  have hdegL : ∀ a : PtVer c v.1 W m, degL (levRel c v.1 W m) a ≤ Fintype.card F + m := fun a => by
    unfold degL
    rw [← BipartiteDD.Regular.ncard_neighborSet_inl]
    exact hdeg.2.1 _
  have hdegR : ∀ b : LnVer c v.1 W m, degR (levRel c v.1 W m) b ≤ Fintype.card F + m := fun b => by
    unfold degR
    rw [← BipartiteDD.Regular.ncard_neighborSet_inr]
    exact hdeg.2.1 _
  have hSdel : ∀ x ∈ delSet v W m (Ldel c Q), Dele c v.1 W m x := fun x hx => (mem_filter.1 hx).2.1
  have hSmem : ∀ x : LnVer c v.1 W m, x ∈ (delSet v W m (Ldel c Q) : Set (LnVer c v.1 W m)) →
      Dele c v.1 W m x :=
    fun x hx => hSdel x (mem_coe.1 hx)
  have hScard := card_delSet_eq v W hc hm Q hQ hQcard
  -- The side sizes: `|β| = |α| + |S|`.
  have hS : Fintype.card (PtVer c v.1 W m) + (delSet v W m (Ldel c Q)).card =
      Fintype.card (LnVer c v.1 W m) := by
    have h := (natCard_sides hc hm v hW hWc).2
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
    have hq : Fintype.card F ≤ Fintype.card F ^ 3 := Nat.le_self_pow (by norm_num) _
    rw [hScard]
    have e : Fintype.card F ^ 3 - Fintype.card F + m + Fintype.card F = Fintype.card F ^ 3 + m := by
      omega
    have e2 : (m - 1) * m * (Fintype.card F ^ 3 - Fintype.card F + m) + (m - 1) * m * Fintype.card F =
        (m - 1) * m * (Fintype.card F ^ 3 + m) := by
      rw [← mul_add, e]
    omega
  have hclass' := hclass v W hm (Ldel c Q)
  have hsα : ∀ a : PtVer c v.1 W m,
      Fintype.card F + m - degL (restrictR (levRel c v.1 W m) (delSet v W m (Ldel c Q) : Set _)) a ≤ m - 1 := by
    rintro ⟨p, s⟩
    have h := ncard_degL_restrict_ge v W hc hm (delSet v W m (Ldel c Q) : Set _) hSmem p s
    have h' : degL (restrictR (levRel c v.1 W m) (delSet v W m (Ldel c Q) : Set _)) ⟨p, s⟩ =
        {b : {b : LnVer c v.1 W m // b ∉ (delSet v W m (Ldel c Q) : Set _)} |
          levRel c v.1 W m ⟨p, s⟩ b.1}.ncard := rfl
    rw [h']
    omega
  have hsβ : ∀ b : {b : LnVer c v.1 W m // b ∉ (delSet v W m (Ldel c Q) : Set _)},
      Fintype.card F + m - degR (restrictR (levRel c v.1 W m) (delSet v W m (Ldel c Q) : Set _)) b ≤ m - 1 := by
    intro b
    obtain ⟨⟨l, t⟩, hb⟩ := b
    have h := ncard_degR_ge v W hm l t
    have h' : degR (restrictR (levRel c v.1 W m) (delSet v W m (Ldel c Q) : Set _)) ⟨⟨l, t⟩, hb⟩ =
        {a : PtVer c v.1 W m | levRel c v.1 W m a ⟨l, t⟩}.ncard := rfl
    rw [h']
    omega
  -- Deficit bound: the point side loses at least `|S|` edges to `S`, and each deleted version has `q + 1`
  -- neighbours.
  have hsum1 : ∑ a : PtVer c v.1 W m, ((delSet v W m (Ldel c Q)).filter fun b => levRel c v.1 W m a b).card ≤
      ∑ a : PtVer c v.1 W m, (Fintype.card F + m - degL (restrictR (levRel c v.1 W m)
        (delSet v W m (Ldel c Q) : Set _)) a) := by
    refine Finset.sum_le_sum fun a _ => ?_
    have h1 := degL_restrictR_add (levRel c v.1 W m) (delSet v W m (Ldel c Q)) a
    have h2 := hdegL a
    omega
  have hsum2 : ∑ a : PtVer c v.1 W m, ((delSet v W m (Ldel c Q)).filter fun b => levRel c v.1 W m a b).card =
      ∑ b ∈ delSet v W m (Ldel c Q), degR (levRel c v.1 W m) b := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold degR
    rw [ncard_setOf_eq_card_filter, Finset.card_filter]
  have hsum3 : (delSet v W m (Ldel c Q)).card * (Fintype.card F + 1) ≤
      ∑ b ∈ delSet v W m (Ldel c Q), degR (levRel c v.1 W m) b := by
    have := Finset.card_nsmul_le_sum (delSet v W m (Ldel c Q)) (fun b => degR (levRel c v.1 W m) b)
      (Fintype.card F + 1) (fun b _ => by
        obtain ⟨l, t⟩ := b
        exact ncard_degR_ge v W hm l t)
    simpa [smul_eq_mul] using this
  have hbig : 2 * (m - 1) * (Fintype.card F + m + (m - 1) + 1) <
      ∑ a : PtVer c v.1 W m, (Fintype.card F + m - degL (restrictR (levRel c v.1 W m)
        (delSet v W m (Ldel c Q) : Set _)) a) := by
    have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
    have hnum : 2 * (m - 1) * (Fintype.card F + m + (m - 1) + 1) <
        (delSet v W m (Ldel c Q)).card * (Fintype.card F + 1) := by
      rw [hScard]
      exact numeric_bound hq2 hm2
    exact lt_of_lt_of_le hnum (hsum3.trans (hsum2.symm.le.trans hsum1))
  exact regular_of_twin_classes (levRel c v.1 W m) (cls v W)
    (fun b b' h a => levRel_twin hc v b b' (congrArg Subtype.val h) a)
    (Fintype.card F + m) (m - 1) 6 (delSet v W m (Ldel c Q)) hS (fun k => hclass' k)
    (fun a => hdegL a) (fun b => hdegR b) hsα hsβ hbig hdeg.2.2

section Final

/-- **Theorem R (brief step 4).** For odd `q` and `m ≥ 2` there is a `(q + m)`-regular bipartite graph of diameter
at most `6` on `2 (q+1) (q⁴ + q² + 1 + (m - 1)(q³ + m + 1))` vertices. -/
theorem theoremR {m : ℕ} (hm2 : 2 ≤ m) :
    ∃ G : SimpleGraph (Fin (2 * (Fintype.card F + 1) * (Fintype.card F ^ 4 + Fintype.card F ^ 2 + 1 +
        (m - 1) * (Fintype.card F ^ 3 + m + 1)))),
      IsBipartiteRegDiam G (Fintype.card F + m) 6 := by
  obtain ⟨c, c0, c1, hc, -, hW, hcard, -⟩ := theorem4 (F := F)
  haveI : Fintype (SPt F) := Fintype.ofFinite _
  haveI : Fintype (HLine F) := by
    have := finite_hline (F := F)
    exact Fintype.ofFinite _
  obtain ⟨G, hG⟩ := regular_levRel hm2 hc (vS c) hW hcard
  have hcardP : Fintype.card (PtVer c (vS c).1 (Wset c c0 c1) m) =
      (Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4) +
        (m - 1) * ((Fintype.card F ^ 3 + 1) * (Fintype.card F + 1) + m * (Fintype.card F + 1)) := by
    rw [← Nat.card_eq_fintype_card]
    exact (natCard_sides hc (by omega) (vS c) hW hcard).1
  have hfin : 2 * Fintype.card (PtVer c (vS c).1 (Wset c c0 c1) m) =
      2 * (Fintype.card F + 1) * (Fintype.card F ^ 4 + Fintype.card F ^ 2 + 1 +
        (m - 1) * (Fintype.card F ^ 3 + m + 1)) := by
    rw [hcardP]
    generalize m - 1 = k
    ring
  exact ⟨G.comap (finCongr hfin).symm, hG.comap (finCongr hfin)⟩

/-- **Theorem R, `m = 2`.** For odd `q` there is a `(q + 2)`-regular bipartite graph of diameter at most `6` on
`2 (q+1) (q⁴ + q³ + q² + 4)` vertices. -/
theorem theoremR_two :
    ∃ G : SimpleGraph (Fin (2 * (Fintype.card F + 1) *
        (Fintype.card F ^ 4 + Fintype.card F ^ 3 + Fintype.card F ^ 2 + 4))),
      IsBipartiteRegDiam G (Fintype.card F + 2) 6 := by
  obtain ⟨G, hG⟩ := theoremR (F := F) (m := 2) le_rfl
  have e : 2 * (Fintype.card F + 1) * (Fintype.card F ^ 4 + Fintype.card F ^ 2 + 1 +
      (2 - 1) * (Fintype.card F ^ 3 + 2 + 1)) =
      2 * (Fintype.card F + 1) * (Fintype.card F ^ 4 + Fintype.card F ^ 3 + Fintype.card F ^ 2 + 4) := by
    rw [show (2 : ℕ) - 1 = 1 from rfl]
    ring
  exact ⟨G.comap (finCongr e).symm, hG.comap (finCongr e)⟩

end Final

end BipartiteDD.HexagonD
