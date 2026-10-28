import BipartiteDD.LeanMaxx.Omega2.Sphere
import BipartiteDD.LeanMaxx.Omega2.Count
import BipartiteDD.LeanMaxx.Omega2.Trace

/-!
# Labels reachable by a short projected walk

`B` is the incidence graph of a generalized hexagon of order `(q, q)` (`HexData`), `π` an involution that
swaps the two colour classes (the partner map "point `t` ↔ line `σ t`").
For a label `a` with partner `π a`, a label `w` at distance `6` from `a` (an "opposite" label) is not
reached by any trace with `≤ 1` ... switches, even many edges and cost `m + 2k ≤ 6` unless `w` lies in
`X1 (π a) ∪ X2 a`; these two sets have fewer than `q⁵` elements (`card_X1_add_card_X2_lt`), so some
opposite label is not reached (`exists_far`).
-/

set_option linter.unusedSectionVars false

namespace BipartiteDD.LeanMaxx.Omega2

open SimpleGraph Finset

/-- Data of a generalized hexagon of order `(q, q)` with a proper 2-colouring. -/
structure HexData {β : Type*} [Fintype β] (B : SimpleGraph β) [DecidableRel B.Adj] (q : ℕ)
    (κ : β → ZMod 2) : Prop where
  egirth : B.egirth = ((2 * 6 : ℕ) : ℕ∞)
  reach : ∀ u v : β, B.Reachable u v
  deg : ∀ v, B.degree v = q + 1
  col : ∀ u v, B.Adj u v → κ u ≠ κ v

variable {β : Type*} [Fintype β] [DecidableEq β] {B : SimpleGraph β} [DecidableRel B.Adj]
  {q : ℕ} {κ : β → ZMod 2}

theorem HexData.card_sph_eq (H : HexData B q κ) (u : β) {d : ℕ} (hd : d ≤ 5) :
    (sph B u d).card = sB q d := by
  induction d with
  | zero => simp [sB, card_sph_zero H.reach]
  | succ d ih =>
    rcases d with _ | d
    · simp [sB, card_sph_one H.deg]
    · have h := card_sph_succ H.col H.deg H.egirth H.reach (u := u) (e := d) (by omega)
      rw [h, ih (by omega)]
      simp [sB]
      ring

theorem HexData.card_sph_six (H : HexData B q κ) (hq : 1 ≤ q) (u : β) : q ^ 5 ≤ (sph B u 6).card :=
  q_pow_five_le_card_sph_six H.col H.deg H.egirth H.reach hq

theorem card_biUnion_le_mul {α γ : Type*} [DecidableEq γ] (s : Finset α) (t : α → Finset γ) {m : ℕ}
    (h : ∀ x ∈ s, (t x).card ≤ m) : (s.biUnion t).card ≤ s.card * m :=
  (Finset.card_biUnion_le).trans (by
    calc ∑ x ∈ s, (t x).card ≤ ∑ _x ∈ s, m := Finset.sum_le_sum h
      _ = s.card * m := by simp)

section Sets

variable (B) (π : β → β)

/-- Labels reached from `b` by `d₁` steps, a switch, `d₂` steps. -/
noncomputable def W2 (b : β) (d₁ d₂ : ℕ) : Finset β :=
  (sph B b d₁).biUnion fun u => sph B (π u) d₂

/-- Labels reached from `a` by `d₁` steps, a switch, `d₂` steps, a switch, `d₃` steps. -/
noncomputable def W3 (a : β) (d₁ d₂ d₃ : ℕ) : Finset β :=
  (sph B a d₁).biUnion fun u₁ => (sph B (π u₁) d₂).biUnion fun u₂ => sph B (π u₂) d₃

noncomputable def X1 (b : β) : Finset β := pairs1.biUnion fun p => W2 B π b p.1 p.2

noncomputable def X2 (a : β) : Finset β := triples2.biUnion fun t => W3 B π a t.1 t.2.1 t.2.2

variable {B π}

theorem HexData.card_W2 (H : HexData B q κ) (b : β) {d₁ d₂ : ℕ} (h1 : d₁ ≤ 4) (h2 : d₂ ≤ 4) :
    (W2 B π b d₁ d₂).card ≤ sB q d₁ * sB q d₂ := by
  unfold W2
  refine (card_biUnion_le_mul _ _ (m := sB q d₂) fun u _ => (H.card_sph_eq _ (by omega)).le).trans ?_
  rw [H.card_sph_eq _ (by omega)]

theorem HexData.card_W3 (H : HexData B q κ) (a : β) {d₁ d₂ d₃ : ℕ} (h1 : d₁ ≤ 4) (h2 : d₂ ≤ 4)
    (h3 : d₃ ≤ 4) : (W3 B π a d₁ d₂ d₃).card ≤ sB q d₁ * (sB q d₂ * sB q d₃) := by
  unfold W3
  refine (card_biUnion_le_mul _ _ (m := sB q d₂ * sB q d₃) fun u₁ _ => ?_).trans ?_
  · refine (card_biUnion_le_mul _ _ (m := sB q d₃) fun u₂ _ => (H.card_sph_eq _ (by omega)).le).trans ?_
    rw [H.card_sph_eq _ (by omega)]
  · rw [H.card_sph_eq _ (by omega)]

theorem HexData.card_X1 (H : HexData B q κ) (b : β) : (X1 B π b).card ≤ sumA q := by
  unfold X1 sumA
  refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun p hp => ?_)
  have hp' := hp
  unfold pairs1 at hp'
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp'
  exact H.card_W2 b (by omega) (by omega)

theorem HexData.card_X2 (H : HexData B q κ) (a : β) : (X2 B π a).card ≤ sumB q := by
  unfold X2 sumB
  refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun t hp => ?_)
  have hp' := hp
  unfold triples2 at hp'
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp'
  have := H.card_W3 (π := π) a (d₁ := t.1) (d₂ := t.2.1) (d₃ := t.2.2) (by omega) (by omega) (by omega)
  rw [← mul_assoc] at this
  exact this

end Sets

section Bad

variable {π : β → β}

/-- Key reach lemma. A trace of cost `m + 2k ≤ 6` (`m` even, `1 ≤ k`, `s ≤ k` switches) from `a` or `π a`
cannot end at a label `w` with `dist a w = 6` unless `w ∈ X1 (π a) ∪ X2 a`. -/
theorem HexData.reach_bad (H : HexData B q κ) (hπ : ∀ a, π (π a) = a)
    (hκπ : ∀ a, κ (π a) = κ a + 1) {a w s0 : β} {m k s : ℕ} (hw : B.dist a w = 6)
    (hs0 : s0 = a ∨ s0 = π a) (ht : Tr B π m s s0 w) (hm : Even m) (hsk : s ≤ k) (hk1 : 1 ≤ k)
    (hb : m + 2 * k ≤ 6) : w ∈ X1 B π (π a) ∪ X2 B π a := by
  have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
  have hκw : κ w = κ a := by
    have := col_dist H.col (H.reach a w)
    rw [hw] at this
    rw [this]
    have h6 : ((6 : ℕ) : ZMod 2) = 0 := by decide
    rw [h6, add_zero]
  have hmz : ((m : ℕ) : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff_even).mpr hm
  have hc := ht.col H.col hκπ
  rw [hκw, hmz, add_zero] at hc
  have hs3 : s ≤ 3 := by omega
  interval_cases s
  · -- no switch
    have hs0a : s0 = a := by
      rcases hs0 with h | h
      · exact h
      · exfalso; rw [h, hκπ] at hc; revert hc; generalize κ a = x; revert x; decide
    subst hs0a
    obtain ⟨p, hp⟩ := ht.walk0
    have := dist_le p
    omega
  · -- one switch
    simp only [Nat.cast_one] at hc
    have hs0a : s0 = π a := by
      rcases hs0 with h | h
      · exfalso; subst h; revert hc; generalize κ s0 = x; revert x; decide
      · exact h
    subst hs0a
    obtain ⟨e, m', u, hmem, ⟨p, hp⟩, ht'⟩ := Tr.decomp (s := 0) ht
    obtain ⟨p2, hp2⟩ := ht'.walk0
    have hd1 : B.dist (π a) u ≤ e := hp ▸ dist_le p
    have hd2 : B.dist (π u) w ≤ m' := hp2 ▸ dist_le p2
    have h2' : (2 : ZMod 2) = 0 := by decide
    have hpar : (((B.dist (π a) u + B.dist (π u) w : ℕ)) : ZMod 2) = 0 := by
      have e1 := col_dist H.col (H.reach (π a) u)
      have e2 := col_dist H.col (H.reach (π u) w)
      have e3 := hκπ u
      have e4 := hκπ a
      push_cast
      linear_combination -e1 - e2 - e3 - e4 + hκw - h2'
    have hev := (ZMod.natCast_eq_zero_iff_even).mp hpar
    apply Finset.mem_union_left
    unfold X1
    rw [Finset.mem_biUnion]
    refine ⟨(B.dist (π a) u, B.dist (π u) w), ?_, ?_⟩
    · unfold pairs1
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, by omega⟩, by omega, hev⟩
    · unfold W2
      rw [Finset.mem_biUnion]
      exact ⟨u, by simp [mem_sph], by simp [mem_sph]⟩
  · -- two switches
    simp only [h2, add_zero] at hc
    have hs0a : s0 = a := by
      rcases hs0 with h | h
      · exact h
      · exfalso; subst h; rw [hκπ] at hc; revert hc; generalize κ a = x; revert x; decide
    subst hs0a
    obtain ⟨e₁, m₁, u₁, hm1, ⟨p₁, hp₁⟩, ht₁⟩ := Tr.decomp (s := 1) ht
    obtain ⟨e₂, m₂, u₂, hm2, ⟨p₂, hp₂⟩, ht₂⟩ := Tr.decomp (s := 0) ht₁
    obtain ⟨p₃, hp₃⟩ := ht₂.walk0
    have hd1 : B.dist s0 u₁ ≤ e₁ := hp₁ ▸ dist_le p₁
    have hd2 : B.dist (π u₁) u₂ ≤ e₂ := hp₂ ▸ dist_le p₂
    have hd3 : B.dist (π u₂) w ≤ m₂ := hp₃ ▸ dist_le p₃
    apply Finset.mem_union_right
    unfold X2
    rw [Finset.mem_biUnion]
    refine ⟨(B.dist s0 u₁, B.dist (π u₁) u₂, B.dist (π u₂) w), ?_, ?_⟩
    · unfold triples2
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, by omega, by omega⟩, by omega⟩
    · unfold W3
      rw [Finset.mem_biUnion]
      refine ⟨u₁, by simp [mem_sph], ?_⟩
      rw [Finset.mem_biUnion]
      exact ⟨u₂, by simp [mem_sph], by simp [mem_sph]⟩
  · -- three switches: no edges are left, `w = a`
    have h3 : ((3 : ℕ) : ZMod 2) = 1 := by decide
    simp only [h3] at hc
    have hs0a : s0 = π a := by
      rcases hs0 with h | h
      · exfalso; subst h; revert hc; generalize κ s0 = x; revert x; decide
      · exact h
    subst hs0a
    obtain rfl : m = 0 := by omega
    have := ht.zero_edges
    simp only [Function.iterate_succ_apply', Function.iterate_zero, id, hπ] at this
    subst this
    simp at hw

/-- Some label opposite to `a` is not in `X1 (π a) ∪ X2 a`: the counting bound `A + B + 1 < q⁵`. -/
theorem HexData.exists_far (H : HexData B q κ) (hq : 7 ≤ q) (a : β) :
    ∃ w, B.dist a w = 6 ∧ w ∉ X1 B π (π a) ∪ X2 B π a := by
  by_contra hcon
  push_neg at hcon
  have hsub : sph B a 6 ⊆ X1 B π (π a) ∪ X2 B π a := fun w hw => hcon w (mem_sph.mp hw)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (X1 B π (π a)) (X2 B π a)
  have h3 := H.card_X1 (π := π) (π a)
  have h4 := H.card_X2 (π := π) a
  have h5 := H.card_sph_six (by omega) a
  have h6 := count_lt hq
  omega

end Bad

end BipartiteDD.LeanMaxx.Omega2
