import BipartiteDD.HexagonD.GCubic

/-! Theorem D, slice 2, part 20 (target 4): `|Wset| = q²(q² - 1)`.

* the `q` points of a line `l ⊄ Π` off `Π` (`ncard_offPi`);
* the points off `Π` collinear with `v` number `q²(q + 1)` (`ncard_notFree`), the free points
  `q³(q² - 1)` (`ncard_free`);
* every free point is on exactly one line of `Wset`, and the `q` off-`Π` points of such a line are free, so
  `q |Wset| = q³(q² - 1)` (`ncard_wset`). -/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon Module Submodule
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)] {c : F}

/-- Double counting by fibres. -/
theorem ncard_fiberwise {α β : Type*} [Finite α] [Finite β] (S : Set α) (T : Set β) (f : α → β)
    (hf : ∀ a ∈ S, f a ∈ T) (k : ℕ) (hk : ∀ t ∈ T, {a | a ∈ S ∧ f a = t}.ncard = k) :
    S.ncard = k * T.ncard := by
  haveI := Fintype.ofFinite α
  haveI := Fintype.ofFinite β
  rw [Set.ncard_eq_toFinset_card' S, Set.ncard_eq_toFinset_card' T]
  have hf' : ∀ a ∈ S.toFinset, f a ∈ T.toFinset := fun a ha => by
    simpa using hf a (by simpa using ha)
  rw [Finset.card_eq_sum_card_fiberwise hf']
  have : ∀ t ∈ T.toFinset, (S.toFinset.filter (fun a => f a = t)).card = k := by
    intro t ht
    have := hk t (by simpa using ht)
    rw [Set.ncard_eq_toFinset_card'] at this
    convert this using 2
    ext a; simp
  rw [Finset.sum_congr rfl this]
  simp [mul_comm]

/-- A line not in `Π` has exactly `q` points off `Π`. -/
theorem ncard_offPi (hc : ¬ IsSquare (-c)) {l : HLine F} (hl : ¬ InPi c l) :
    {p : SPt F | hexInc p l ∧ ¬ OnPi c p}.ncard = Fintype.card F := by
  have h1 : {p : SPt F | hexInc p l ∧ OnPi c p}.ncard = 1 := by
    rw [Set.ncard_eq_one]
    obtain ⟨p, hp, hpl⟩ := exists_piPt c l
    refine ⟨p, ?_⟩
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hq, hqPi⟩
      exact eq_of_onPi_of_not_inPi hqPi hp hq hpl hl
    · rintro rfl
      exact ⟨hpl, hp⟩
  have h2 : {p : SPt F | hexInc p l}.ncard = Fintype.card F + 1 := ncard_hexInc_points l
  have hu : {p : SPt F | hexInc p l} =
      {p : SPt F | hexInc p l ∧ OnPi c p} ∪ {p : SPt F | hexInc p l ∧ ¬ OnPi c p} := by
    ext p; simp only [Set.mem_setOf_eq, Set.mem_union]; tauto
  have hd : Disjoint {p : SPt F | hexInc p l ∧ OnPi c p} {p : SPt F | hexInc p l ∧ ¬ OnPi c p} := by
    rw [Set.disjoint_left]
    rintro p ⟨-, h1⟩ ⟨-, h2⟩
    exact h2 h1
  rw [hu, Set.ncard_union_eq hd, h1] at h2
  omega

/-- The points off `Π` collinear (by a line) with a point of `v`. -/
def NotFree (c : F) : Set (SPt F) :=
  {p | ¬ OnPi c p ∧ ∃ M : HLine F, hexInc p M ∧ Meets (vStd : HLine F) M}

/-- The free points. -/
def FreePts (c : F) : Set (SPt F) :=
  {p | ¬ OnPi c p ∧ ¬ ∃ M : HLine F, hexInc p M ∧ Meets (vStd : HLine F) M}

theorem ncard_notFree (hc : ¬ IsSquare (-c)) :
    (NotFree c).ncard = Fintype.card F ^ 2 * (Fintype.card F + 1) := by
  have hpv : ∀ p : SPt F, ¬ OnPi c p → ¬ hexInc p (vStd : HLine F) := fun p hp h =>
    hp (vStd_inPi c _ h)
  -- the line through a point of `NotFree`
  let g : SPt F → HLine F := fun p =>
    if h : ∃ M : HLine F, hexInc p M ∧ Meets (vStd : HLine F) M then h.choose else vStd
  have hg : ∀ p ∈ NotFree c, hexInc p (g p) ∧ Meets (vStd : HLine F) (g p) := by
    intro p hp
    have h := hp.2
    simp only [g, dif_pos h]
    exact h.choose_spec
  have hT : ∀ p ∈ NotFree c, g p ∈ {M : HLine F | Meets (vStd : HLine F) M ∧ ¬ InPi c M} := by
    intro p hp
    obtain ⟨h1, h2⟩ := hg p hp
    refine ⟨h2, fun hi => hp.1 (hi _ h1)⟩
  have := ncard_fiberwise (NotFree c) {M : HLine F | Meets (vStd : HLine F) M ∧ ¬ InPi c M} g hT
    (Fintype.card F) (by
      rintro M ⟨hM1, hM2⟩
      have : {a | a ∈ NotFree c ∧ g a = M} = {p : SPt F | hexInc p M ∧ ¬ OnPi c p} := by
        ext p
        simp only [Set.mem_setOf_eq]
        constructor
        · rintro ⟨hp, rfl⟩
          exact ⟨(hg p hp).1, hp.1⟩
        · rintro ⟨hpM, hpPi⟩
          have hp : p ∈ NotFree c := ⟨hpPi, M, hpM, hM1⟩
          refine ⟨hp, ?_⟩
          obtain ⟨h1, ⟨r, hr, hr'⟩⟩ := hg p hp
          obtain ⟨r', hr'v, hr'M⟩ := hM1
          exact eq_of_triangle genPolygonGraph_hexagon (hpv p hpPi) h1 hr' hr hpM hr'M hr'v
      rw [this]
      exact ncard_offPi hc hM2)
  rw [this]
  have hm := ncard_meets hc (vS c)
  have hm' : {M : HLine F | Meets (vStd : HLine F) M ∧ ¬ InPi c M}.ncard =
      Fintype.card F * (Fintype.card F + 1) := hm
  rw [hm']
  ring

theorem ncard_free (hc : ¬ IsSquare (-c)) :
    (FreePts c).ncard + Fintype.card F ^ 2 * (Fintype.card F + 1) +
      (Fintype.card F ^ 3 + 1) * (Fintype.card F + 1) =
      (Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4) := by
  have hu : (Set.univ : Set (SPt F)) = {p | OnPi c p} ∪ NotFree c ∪ FreePts c := by
    ext p
    simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq, NotFree, FreePts, true_iff]
    by_cases h1 : OnPi c p <;> by_cases h2 : ∃ M : HLine F, hexInc p M ∧ Meets (vStd : HLine F) M <;>
      simp [h1, h2]
  have hd1 : Disjoint {p : SPt F | OnPi c p} (NotFree c) := by
    rw [Set.disjoint_left]; rintro p h1 ⟨h2, -⟩; exact h2 h1
  have hd2 : Disjoint ({p : SPt F | OnPi c p} ∪ NotFree c) (FreePts c) := by
    rw [Set.disjoint_left]
    rintro p (h1 | ⟨h1, h2⟩) ⟨h3, h4⟩
    · exact h3 h1
    · exact h4 h2
  have := congrArg Set.ncard hu
  rw [Set.ncard_univ, Set.ncard_union_eq hd2, Set.ncard_union_eq hd1, ncard_onPi hc,
    ncard_notFree hc, card_spt_eq] at this
  omega

theorem ncard_wset (hc : ¬ IsSquare (-c)) {c0 c1 : F} (hG : GoodCubic c c0 c1) :
    (Wset c c0 c1).ncard + Fintype.card F ^ 2 = Fintype.card F ^ 4 := by
  have hq : 0 < Fintype.card F := Fintype.card_pos
  let g : SPt F → HLine F := fun p =>
    if h : p ∈ FreePts c then (exists_unique_wline hc hG h.1 h.2).exists.choose else vStd
  have hg : ∀ p ∈ FreePts c, g p ∈ Wset c c0 c1 ∧ hexInc p (g p) := by
    intro p hp
    simp only [g, dif_pos hp]
    exact (exists_unique_wline hc hG hp.1 hp.2).exists.choose_spec
  have hfree_of_mem : ∀ w ∈ Wset c c0 c1, ∀ p : SPt F, hexInc p w → ¬ OnPi c p → p ∈ FreePts c := by
    intro w hw p hpw hp
    refine ⟨hp, ?_⟩
    rintro ⟨M, hpM, r, hrv, hrM⟩
    exact (wset_whiskers hc hG).opp w hw ⟨r, M, p, hrv, hrM, hpM, hpw⟩ |>.elim
  have := ncard_fiberwise (FreePts c) (Wset c c0 c1) g (fun p hp => (hg p hp).1) (Fintype.card F) (by
    intro w hw
    have : {a | a ∈ FreePts c ∧ g a = w} = {p : SPt F | hexInc p w ∧ ¬ OnPi c p} := by
      ext p
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨hp, rfl⟩
        exact ⟨(hg p hp).2, hp.1⟩
      · rintro ⟨hpw, hpPi⟩
        have hp := hfree_of_mem w hw p hpw hpPi
        refine ⟨hp, ?_⟩
        obtain ⟨m, -, huniq⟩ := exists_unique_wline hc hG hp.1 hp.2
        exact (huniq _ (hg p hp)).trans (huniq _ ⟨hw, hpw⟩).symm
    rw [this]
    exact ncard_offPi hc (fun hi => (wset_whiskers hc hG).not_inPi w hw hi))
  have h2 := ncard_free hc (c := c)
  rw [this] at h2
  have e : Fintype.card F * (Wset c c0 c1).ncard + Fintype.card F ^ 2 * (Fintype.card F + 1) +
      (Fintype.card F ^ 3 + 1) * (Fintype.card F + 1) =
      (Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4) := h2
  have : Fintype.card F * ((Wset c c0 c1).ncard + Fintype.card F ^ 2) = Fintype.card F * Fintype.card F ^ 4 := by
    nlinarith [e]
  exact Nat.eq_of_mul_eq_mul_left hq this

end BipartiteDD.HexagonD
