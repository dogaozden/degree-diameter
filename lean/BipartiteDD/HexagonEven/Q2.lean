import BipartiteDD.HexagonEven.Delorme
import BipartiteDD.HexagonEven.Reg.Final

/-! Theorem D for `q = 2` (characteristic `2`, `d = 1`): an explicit set of `12` whiskers.

The whiskers come from the computer search `research/evenq/whiskers_raw_q2.json` (`delta = 1`, spread line
`v = <e1, e6>`). Each whisker `W_i` is the line `span {wC i, wE i}` of `H(2)`; its three points are `wC i`,
`wE i` and `wC i + wE i` (over `ZMod 2`). The coordinates were read off the Python points of
`research/evenq/hexq.py`, which use the same coordinates as `Hexagon.Defs` (`Qf`, `Bf`, `Tits`).

Everything finite is checked by `decide` on `Fin 7 → ZMod 2` and `Fin 12`; ordinary kernel `decide` only. -/

namespace BipartiteDD.HexagonEven

open BipartiteDD.Hexagon Module Submodule

/-- Vectors of `F⁷` over `F₂`. -/
abbrev V2 := V7 (ZMod 2)

/-! ### The data -/

/-- The spread line `v = ⟨e₁, e₆⟩` (the points `vC`, `vE`, `vC + vE`). -/
def q2vC : V2 := ![0, 1, 0, 0, 0, 0, 0]
def q2vE : V2 := ![0, 0, 0, 0, 0, 0, 1]

/-- First basis vectors of the `12` whiskers. -/
def q2wC : Fin 12 → V2 := ![![0, 0, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0], ![0, 1, 1, 0, 0, 0, 0],
  ![1, 1, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 1, 0, 0], ![0, 1, 1, 0, 1, 0, 0], ![1, 0, 1, 1, 1, 0, 0],
  ![1, 1, 1, 1, 1, 0, 0], ![1, 0, 0, 0, 0, 1, 0], ![0, 1, 0, 1, 0, 1, 0], ![1, 1, 1, 1, 0, 1, 0],
  ![1, 0, 1, 1, 1, 1, 0]]

/-- Second basis vectors of the `12` whiskers. -/
def q2wE : Fin 12 → V2 := ![![0, 0, 0, 0, 1, 1, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 1, 1],
  ![0, 0, 0, 0, 0, 1, 1], ![0, 1, 1, 1, 0, 1, 0], ![0, 0, 1, 1, 0, 1, 1], ![0, 0, 1, 0, 0, 1, 0],
  ![0, 1, 1, 0, 0, 1, 1], ![0, 0, 1, 1, 0, 0, 1], ![1, 0, 1, 0, 1, 0, 1], ![0, 1, 1, 1, 0, 0, 1],
  ![1, 1, 1, 0, 1, 0, 1]]

/-! ### Finite facts (all by `decide`) -/

theorem q2_vC_ne : q2vC ≠ 0 := by decide
theorem q2_vE_ne : q2vE ≠ 0 := by decide
theorem q2_vE_ne_vC : q2vE ≠ q2vC := by decide

theorem q2_vCE_ne : q2vC + q2vE ≠ 0 := by decide

theorem q2_pair_v : IsHPair q2vC q2vE := by
  unfold IsHPair Tits pl Qf Bf q2vC q2vE; decide

set_option maxRecDepth 20000 in
theorem q2_wC_ne : ∀ i : Fin 12, q2wC i ≠ 0 ∧ q2wE i ≠ 0 ∧ q2wE i ≠ q2wC i := by
  unfold q2wC q2wE; decide

set_option maxRecDepth 20000 in
theorem q2_pair_w : ∀ i : Fin 12, IsHPair (q2wC i) (q2wE i) := by
  unfold IsHPair Tits pl Qf Bf q2wC q2wE; decide

set_option maxRecDepth 20000 in
theorem q2_notPi_w : ∀ i : Fin 12,
    ¬ (q2wC i 0 + q2wC i 3 + 1 * q2wC i 4 = 0 ∧ q2wE i 0 + q2wE i 3 + 1 * q2wE i 4 = 0) := by
  unfold q2wC q2wE; decide

set_option maxRecDepth 20000 in
theorem q2_opp_w : ∀ i : Fin 12, ∀ x ∈ [q2vC, q2vE, q2vC + q2vE], ∀ y ∈ [q2wC i, q2wE i, q2wC i + q2wE i],
    ¬ IsHPair x y := by
  unfold IsHPair Tits pl Qf Bf q2vC q2vE q2wC q2wE; decide

set_option maxRecDepth 20000 in
theorem q2_free_w : ∀ i j : Fin 12, i ≠ j → ∀ z ∈ [q2wC i, q2wE i, q2wC i + q2wE i],
    z ∈ [q2wC j, q2wE j, q2wC j + q2wE j] →
    (z 0 + z 3 + 1 * z 4 = 0 ∨ IsHPair z q2vC ∨ IsHPair z q2vE ∨ IsHPair z (q2vC + q2vE)) := by
  unfold IsHPair Tits pl Qf Bf q2vC q2vE q2wC q2wE; decide

set_option maxRecDepth 20000 in
theorem q2_inj_w : ∀ i j : Fin 12, i ≠ j →
    ¬ ((q2wC i = q2wC j ∨ q2wC i = q2wE j ∨ q2wC i = q2wC j + q2wE j) ∧
      (q2wE i = q2wC j ∨ q2wE i = q2wE j ∨ q2wE i = q2wC j + q2wE j)) := by
  unfold q2wC q2wE; decide

/-! ### Lines in `F₂`: span descriptions -/

theorem zmod2_cases (t : ZMod 2) : t = 0 ∨ t = 1 := by revert t; decide

theorem mem_span_pair_disj {a b x : V2} (hx : x ∈ span (ZMod 2) ({a, b} : Set V2)) :
    x = 0 ∨ x = a ∨ x = b ∨ x = a + b := by
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 hx
  rcases zmod2_cases c with rfl | rfl <;> rcases zmod2_cases d with rfl | rfl <;> simp

theorem mem_span_single_disj {a x : V2} (hx : x ∈ span (ZMod 2) ({a} : Set V2)) :
    x = 0 ∨ x = a := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rcases zmod2_cases c with rfl | rfl <;> simp

theorem mem_list3 {a b z : V2} : z ∈ [a, b, a + b] ↔ z = a ∨ z = b ∨ z = a + b := by simp

/-- Two-point lines: a generic lemma giving the list of nonzero points. -/
theorem mem_span_pair_list {a b x : V2} (hx : x ∈ span (ZMod 2) ({a, b} : Set V2)) (hx0 : x ≠ 0) :
    x ∈ [a, b, a + b] := by
  rcases mem_span_pair_disj hx with h | h | h | h
  · exact absurd h hx0
  · exact mem_list3.2 (Or.inl h)
  · exact mem_list3.2 (Or.inr (Or.inl h))
  · exact mem_list3.2 (Or.inr (Or.inr h))

/-- The whisker lines: `W_i = span {wC i, wE i}`. -/
def q2wl (i : Fin 12) : HLine (ZMod 2) :=
  hlineOf (q2_wC_ne i).1 (q2_pair_w i) (fun h => by
    rcases mem_span_single_disj h with h | h
    · exact (q2_wC_ne i).2.1 h
    · exact (q2_wC_ne i).2.2 h)

theorem q2wl_span (i : Fin 12) : (q2wl i).1 = span (ZMod 2) ({q2wC i, q2wE i} : Set V2) := rfl

theorem q2wl_mem_C (i : Fin 12) : q2wC i ∈ (q2wl i).1 := by
  rw [q2wl_span]; exact subset_span (by simp)

theorem q2wl_mem_E (i : Fin 12) : q2wE i ∈ (q2wl i).1 := by
  rw [q2wl_span]; exact subset_span (by simp)

/-- The spread line `v = ⟨e₁, e₆⟩`. -/
def q2vl : HLine (ZMod 2) :=
  hlineOf q2_vC_ne q2_pair_v (fun h => by
    rcases mem_span_single_disj h with h | h
    · exact q2_vE_ne h
    · exact q2_vE_ne_vC h)

theorem q2vl_span : q2vl.1 = span (ZMod 2) ({q2vC, q2vE} : Set V2) := rfl

theorem q2vl_mem_C : q2vC ∈ q2vl.1 := by
  rw [q2vl_span]; exact subset_span (by simp)

theorem q2vl_mem_E : q2vE ∈ q2vl.1 := by
  rw [q2vl_span]; exact subset_span (by simp)

theorem q2vl_mem_CE : q2vC + q2vE ∈ q2vl.1 := by
  rw [q2vl_span]; exact add_mem (subset_span (by simp)) (subset_span (by simp))

theorem q2vl_inPi : InPiE 1 q2vl := by
  intro x hx
  rw [q2vl_span] at hx
  rcases mem_span_pair_disj hx with rfl | rfl | rfl | rfl <;> decide

/-- The spread line `v` as an element of `S_1`. -/
def q2vS : SLineE (1 : ZMod 2) := ⟨q2vl, q2vl_inPi⟩

/-! ### Generic lemmas on two lines -/

/-- Lines `L₁ = span {a, b}` and `L₂ = span {c, e}` with no `IsHPair` between their nonzero points are opposite. -/
theorem opp_of_lines {L1 L2 : HLine (ZMod 2)} {a b c e : V2} (h1 : L1.1 = span (ZMod 2) ({a, b} : Set V2))
    (h2 : L2.1 = span (ZMod 2) ({c, e} : Set V2))
    (hno : ∀ x ∈ [a, b, a + b], ∀ y ∈ [c, e, c + e], ¬ IsHPair x y) :
    HexagonD.Opp (hexInc (F := ZMod 2)) L1 L2 := by
  rintro ⟨p, M, p', hp1, hpM, hp'M, hp'2⟩
  have hx : p.1.rep ∈ span (ZMod 2) ({a, b} : Set V2) := by
    have h : p.1.rep ∈ L1.1 := hp1
    rwa [h1] at h
  have hy : p'.1.rep ∈ span (ZMod 2) ({c, e} : Set V2) := by
    have h : p'.1.rep ∈ L2.1 := hp'2
    rwa [h2] at h
  have hI : IsHPair p.1.rep p'.1.rep := M.2.2 _ hpM _ hp'M
  exact hno _ (mem_span_pair_list hx p.1.rep_nonzero) _ (mem_span_pair_list hy p'.1.rep_nonzero) hI

/-- A whisker meeting a point `p` off `Π` through an `IsHPair` with a point of `v`: `p` lies on a line meeting `v`. -/
theorem meets_of_hpair {p : SPt (ZMod 2)} {r : V2} (hr0 : r ≠ 0) (hQr : Qf r = 0)
    (hpr : IsHPair p.1.rep r) (hr : r ∈ q2vl.1) :
    ∃ M : HLine (ZMod 2), hexInc p M ∧ Meets q2vl M := by
  obtain ⟨M, hpM, hrM⟩ := exists_hline_of_isHPair_even p.1.rep_nonzero hpr
  exact ⟨M, hpM, sptOf r hr0 hQr, sptOf_mem.2 hr, sptOf_mem.2 hrM⟩

/-! ### The whisker set and its properties -/

/-- The `12` whiskers. -/
def q2W : Set (HLine (ZMod 2)) := Set.range q2wl

theorem q2wl_inj : Function.Injective q2wl := by
  intro i j h
  by_contra hij
  have h1 : q2wC i ∈ (q2wl j).1 := by rw [← h]; exact q2wl_mem_C i
  have h2 : q2wE i ∈ (q2wl j).1 := by rw [← h]; exact q2wl_mem_E i
  rw [q2wl_span] at h1 h2
  apply q2_inj_w i j hij
  constructor
  · rcases mem_span_pair_disj h1 with h' | h' | h' | h'
    · exact absurd h' (q2_wC_ne i).1
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')
  · rcases mem_span_pair_disj h2 with h' | h' | h' | h'
    · exact absurd h' (q2_wC_ne i).2.1
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')

theorem q2W_ncard : q2W.ncard = 12 := by
  rw [q2W, Set.ncard_range_of_injective q2wl_inj, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **The `q = 2` whisker set is a set of whiskers** for the spread line `v = ⟨e₁, e₆⟩`, `d = 1`. -/
theorem q2_whiskers : Whiskers (1 : ZMod 2) q2vS q2W where
  not_inPi := by
    rintro _ ⟨i, rfl⟩ h
    exact q2_notPi_w i ⟨h _ (q2wl_mem_C i), h _ (q2wl_mem_E i)⟩
  opp := by
    rintro _ ⟨i, rfl⟩
    exact opp_of_lines (L1 := q2vl) (L2 := q2wl i) rfl rfl (q2_opp_w i)
  free := by
    intro p hp hM w hw w' hw' hpw hpw'
    obtain ⟨i, rfl⟩ := hw
    obtain ⟨j, rfl⟩ := hw'
    by_contra hij
    have hij' : i ≠ j := fun h => hij (by rw [h])
    have hxi : p.1.rep ∈ [q2wC i, q2wE i, q2wC i + q2wE i] :=
      mem_span_pair_list (show p.1.rep ∈ span (ZMod 2) ({q2wC i, q2wE i} : Set V2) from hpw)
        p.1.rep_nonzero
    have hxj : p.1.rep ∈ [q2wC j, q2wE j, q2wC j + q2wE j] :=
      mem_span_pair_list (show p.1.rep ∈ span (ZMod 2) ({q2wC j, q2wE j} : Set V2) from hpw')
        p.1.rep_nonzero
    rcases q2_free_w i j hij' _ hxi hxj with h | h | h | h
    · exact hp h
    · exact hM (meets_of_hpair q2_vC_ne (by unfold Qf q2vC; decide) h q2vl_mem_C)
    · exact hM (meets_of_hpair q2_vE_ne (by unfold Qf q2vE; decide) h q2vl_mem_E)
    · exact hM (meets_of_hpair q2_vCE_ne (by unfold Qf q2vC q2vE; decide) h q2vl_mem_CE)

/-! ### Exactness: every free point lies on exactly one whisker -/

/-- A nonzero singular point off `Π` with no `IsHPair` to a point of `v` (equivalently: a free point). -/
abbrev q2Good (x : V2) : Prop :=
  x ≠ 0 ∧ Qf x = 0 ∧ x 0 + x 3 + 1 * x 4 ≠ 0 ∧ ¬ IsHPair x q2vC ∧ ¬ IsHPair x q2vE ∧
    ¬ IsHPair x (q2vC + q2vE)

/-- Some whisker contains the point. -/
abbrev q2Cov (x : V2) : Prop :=
  ∃ i : Fin 12, x = q2wC i ∨ x = q2wE i ∨ x = q2wC i + q2wE i

set_option maxRecDepth 20000 in
/-- Finite check over `F₂⁷` (nested quantifiers over `ZMod 2`, to keep `decide` cheap). -/
theorem q2_cover_dec : ∀ a0 a1 a2 a3 a4 a5 a6 : ZMod 2,
    q2Good ![a0, a1, a2, a3, a4, a5, a6] → q2Cov ![a0, a1, a2, a3, a4, a5, a6] := by
  unfold q2Good q2Cov IsHPair Tits pl Qf Bf q2vC q2vE q2wC q2wE; decide

theorem q2_cover_all (x : V2) (h : q2Good x) : q2Cov x := by
  have key := q2_cover_dec (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)
  have hx : (![x 0, x 1, x 2, x 3, x 4, x 5, x 6] : V2) = x := by
    ext j; fin_cases j <;> rfl
  rw [hx] at key
  exact key h

theorem q2wl_mem_of {i : Fin 12} {x : V2} (h : x = q2wC i ∨ x = q2wE i ∨ x = q2wC i + q2wE i) :
    x ∈ (q2wl i).1 := by
  rcases h with rfl | rfl | rfl
  · exact q2wl_mem_C i
  · exact q2wl_mem_E i
  · rw [q2wl_span]; exact add_mem (subset_span (by simp)) (subset_span (by simp))

/-- **Exactness for `q = 2`**: every free point off `Π` (no line through it meets `v`) lies on exactly one
whisker of `q2W`. -/
theorem q2_exact (p : SPt (ZMod 2)) (hp : ¬ OnPiE 1 p)
    (hfree : ¬ ∃ M : HLine (ZMod 2), hexInc p M ∧ Meets q2vl M) :
    ∃! m : HLine (ZMod 2), m ∈ q2W ∧ hexInc p m := by
  have hgood : q2Good p.1.rep := ⟨p.1.rep_nonzero, p.2, fun h => hp h,
    fun h => hfree (meets_of_hpair q2_vC_ne (by unfold Qf q2vC; decide) h q2vl_mem_C),
    fun h => hfree (meets_of_hpair q2_vE_ne (by unfold Qf q2vE; decide) h q2vl_mem_E),
    fun h => hfree (meets_of_hpair q2_vCE_ne (by unfold Qf q2vC q2vE; decide) h q2vl_mem_CE)⟩
  obtain ⟨i, hi⟩ := q2_cover_all _ hgood
  have hpi : hexInc p (q2wl i) := q2wl_mem_of hi
  refine ⟨q2wl i, ⟨⟨i, rfl⟩, hpi⟩, fun m hm => ?_⟩
  exact q2_whiskers.free p hp hfree m hm.1 (q2wl i) ⟨i, rfl⟩ hm.2 hpi

/-! ### The regular instance -/

/-- **Theorem R for `q = 2`, `m = 2`**: a `4`-regular bipartite graph of diameter `6` on `192` vertices. -/
theorem theoremR_q2 : ∃ G : SimpleGraph (Fin 192), IsBipartiteRegDiam G 4 6 := by
  have hd : ∀ t : ZMod 2, t ^ 2 + t + 1 ≠ 0 := by decide
  have hchar : (2 : ZMod 2) = 0 := by decide
  have : Fintype (SPt (ZMod 2)) := Fintype.ofFinite _
  have : Fintype (HLine (ZMod 2)) := by
    have := finite_hline_even (F := ZMod 2)
    exact Fintype.ofFinite _
  have hWc : q2W.ncard + Fintype.card (ZMod 2) ^ 2 = Fintype.card (ZMod 2) ^ 4 := by
    rw [q2W_ncard, ZMod.card]; norm_num
  obtain ⟨G, hG⟩ := regular_levRel (m := 2) le_rfl hd hchar q2vS q2_whiskers hWc
  have hcardP : Fintype.card (PtVer 1 q2vS.1 q2W 2) = 96 := by
    rw [← Nat.card_eq_fintype_card, (natCard_sides hd hchar (by norm_num) q2vS q2_whiskers hWc).1]
    simp only [ZMod.card]
    norm_num
  have hfin : 2 * Fintype.card (PtVer 1 q2vS.1 q2W 2) = 192 := by
    rw [hcardP]
  rw [ZMod.card] at hG
  exact ⟨G.comap (finCongr hfin).symm, hG.comap (finCongr hfin)⟩

/-- Transfer along an equality of vertex counts. -/
theorem isBDD_transfer {n m : ℕ} (h : n = m) (H : SimpleGraph (Fin n)) {a b : ℕ}
    (hH : IsBipartiteDegDiam H a b) : ∃ H' : SimpleGraph (Fin m), IsBipartiteDegDiam H' a b := by
  subst h
  exact ⟨H, hH⟩

/-- **Theorem D for `q = 2`**: `n_b(4, 6) ≥ 208`, i.e. a graph on `208` vertices of maximum degree `4` and
diameter `6` (bipartite), from Delorme's levels with the `12` whiskers `q2W` (`m = 2`, `q = 2`). -/
theorem theoremD_q2 : ∃ H : SimpleGraph (Fin 208), IsBipartiteDegDiam H 4 6 := by
  have hd : ∀ t : ZMod 2, t ^ 2 + t + 1 ≠ 0 := by decide
  have hchar : (2 : ZMod 2) = 0 := by decide
  obtain ⟨H, hH⟩ := whiskers_bound_hexagon (F := ZMod 2) (d := 1) hd hchar (m := 2) (by norm_num)
    q2vS q2_whiskers
  have h4 : ∀ k : ℕ, k = 4 → IsBipartiteDegDiam H k 6 → IsBipartiteDegDiam H 4 6 := by
    rintro k rfl h; exact h
  refine isBDD_transfer ?_ H (h4 _ (by rw [ZMod.card]) hH)
  norm_num [ZMod.card, q2W_ncard]

end BipartiteDD.HexagonEven
