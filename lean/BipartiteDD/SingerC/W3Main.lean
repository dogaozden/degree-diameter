import BipartiteDD.SingerC.W3Ovoid
import BipartiteDD.GQST.Main

/-! Corollary C1, steps 2–5: the copy theorem applied to W(3,q) with the
2-ovoid `O` and the regular spread. -/

namespace BipartiteDD.SingerC

open Module Projectivization
open scoped LinearAlgebra.Projectivization

namespace Setting

variable {K : Type*} [Field K] [Fintype K] {p : ℕ} [Fact p.Prime] [CharP K p]
variable (S : Setting K p)

noncomputable instance instFintypePt : Fintype (ℙ S.F K) := Fintype.ofFinite _

noncomputable instance instFintypeLine : Fintype S.TILine := Fintype.ofFinite _

noncomputable instance instFintypeSpread : Fintype {V : S.TILine // S.IsSpread V} :=
  Fintype.ofFinite _

/-- `W(3,q)` as a generalized quadrangle of order `(q, q)`. -/
theorem gq_W : BipartiteDD.GQst (ℙ S.F K) S.TILine S.q S.q :=
  ⟨S.pts_on_line, S.lines_on_pt, S.one_line, S.gq_ax⟩

/-- The 2-ovoid meets every line in exactly two points. -/
theorem card_O_line {a : ℕ} (ha : a ≤ S.q) (l : S.TILine) :
    Nat.card {x : ℙ S.F K // x.submodule ≤ l.1 ∧ S.Oz a x.rep} = 2 := by
  have h1 := S.card_vec_points l.1 (S.Oz a) (fun c hc hc0 z => S.Oz_mul_F_iff ha hc hc0)
  have h2 : Nat.card {v : K // v ≠ 0 ∧ v ∈ l.1 ∧ S.Oz a v} = 2 * (S.q - 1) := by
    rw [← S.propC_subspace ha l.1 l.2.1 l.2.2]
    exact (Nat.card_congr
      { toFun := fun u => ⟨u.1.1, fun h => u.2.1 (Subtype.ext h), u.1.2, u.2.2⟩
        invFun := fun v => ⟨⟨v.1, v.2.2.1⟩, fun h => v.2.1 (congrArg Subtype.val h), v.2.2.2⟩
        left_inv := fun u => Subtype.ext (Subtype.ext rfl)
        right_inv := fun v => Subtype.ext rfl }).symm
  rw [h2] at h1
  have hq : 0 < S.q - 1 := by have := S.one_lt_q; omega
  have h3 : (S.q - 1) * 2 =
      (S.q - 1) * Nat.card {x : ℙ S.F K // x.submodule ≤ l.1 ∧ S.Oz a x.rep} := by
    rw [mul_comm]
    omega
  exact (Nat.eq_of_mul_eq_mul_left hq h3).symm

/-- The total number of points: `(q + 1)(q² + 1)`. -/
theorem card_points : Nat.card (ℙ S.F K) = (S.q + 1) * (S.q ^ 2 + 1) := by
  rw [Projectivization.card_of_finrank S.F K S.finrank_K, S.natCard_F]
  simp [Finset.sum_range_succ]
  ring

/-- Points are partitioned by the spread lines. -/
theorem card_partition (R : ℙ S.F K → Prop) :
    Nat.card {x : ℙ S.F K // R x} =
      ∑ V : {V : S.TILine // S.IsSpread V}, Nat.card {x : ℙ S.F K // R x ∧ x ∈ V.1} := by
  classical
  let g : {x : ℙ S.F K // R x} → {V : S.TILine // S.IsSpread V} := fun x =>
    ⟨S.spreadLine x.1.rep_nonzero, x.1.rep, x.1.rep_nonzero, rfl⟩
  have e1 : Nat.card {x : ℙ S.F K // R x} =
      Nat.card (Σ V : {V : S.TILine // S.IsSpread V}, {x : {x : ℙ S.F K // R x} // g x = V}) :=
    (Nat.card_congr (Equiv.sigmaFiberEquiv g)).symm
  rw [e1, Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro V _
  obtain ⟨a, ha, hVa⟩ := V.2
  apply Nat.card_congr
  exact
    { toFun := fun x => ⟨x.1.1, x.1.2, by
        have h1 : S.spreadLine x.1.1.rep_nonzero = V.1 := congrArg (fun w => w.1) x.2
        exact h1 ▸ S.pt_mem_spreadLine x.1.1⟩
      invFun := fun z => ⟨⟨z.1, z.2.1⟩, Subtype.ext (Subtype.ext (by
        have hzV : z.1.rep ∈ S.spreadSub a := by
          have := (S.pt_mem_iff V.1 z.1).mp z.2.2
          rwa [hVa] at this
        show S.spreadSub z.1.rep = V.1.1
        rw [hVa]
        exact S.spreadSub_eq_of_mem hzV z.1.rep_nonzero))⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun z => Subtype.ext rfl }

/-- The number of spread lines: `q² + 1`. -/
theorem card_spread : Nat.card {V : S.TILine // S.IsSpread V} = S.q ^ 2 + 1 := by
  have h := S.card_partition (fun _ => True)
  have hV : ∀ V : {V : S.TILine // S.IsSpread V},
      Nat.card {x : ℙ S.F K // True ∧ x ∈ V.1} = S.q + 1 := fun V => by
    rw [← S.pts_on_line V.1]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩))
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)), S.card_points] at h
  simp only [hV, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  rw [← Nat.card_eq_fintype_card] at h
  have hpos : 0 < S.q + 1 := Nat.succ_pos _
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [← h]
  ring

/-- The 2-ovoid has `2 (q² + 1)` points. -/
theorem card_O {a : ℕ} (ha : a ≤ S.q) : Nat.card {x : ℙ S.F K // S.Oz a x.rep} = 2 * (S.q ^ 2 + 1) := by
  have hV : ∀ V : {V : S.TILine // S.IsSpread V},
      Nat.card {x : ℙ S.F K // S.Oz a x.rep ∧ x ∈ V.1} = 2 := fun V =>
    (Nat.card_congr (Equiv.subtypeEquivRight (fun x => and_comm))).trans (S.card_O_line ha V.1)
  rw [S.card_partition (fun x => S.Oz a x.rep)]
  simp only [hV, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, S.card_spread, mul_comm]

/-- The lines are as many as the points: `(q + 1)(q² + 1)`. -/
theorem card_lines : Nat.card S.TILine = (S.q + 1) * (S.q ^ 2 + 1) := by
  classical
  have hP : ∀ l : S.TILine, Nat.card {x : ℙ S.F K // x ∈ l} = ∑ x : ℙ S.F K, if x ∈ l then 1 else 0 := by
    intro l
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  have hL : ∀ x : ℙ S.F K, Nat.card {l : S.TILine // x ∈ l} = ∑ l : S.TILine, if x ∈ l then 1 else 0 := by
    intro x
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  have key : ∑ l : S.TILine, ∑ x : ℙ S.F K, (if x ∈ l then 1 else 0) =
      ∑ x : ℙ S.F K, ∑ l : S.TILine, (if x ∈ l then 1 else 0) := Finset.sum_comm
  have h1 : ∑ l : S.TILine, Nat.card {x : ℙ S.F K // x ∈ l} = Nat.card S.TILine * (S.q + 1) := by
    rw [Finset.sum_congr rfl (fun l _ => S.pts_on_line l), Finset.sum_const, Finset.card_univ,
      Nat.card_eq_fintype_card, smul_eq_mul]
  have h2 : ∑ x : ℙ S.F K, Nat.card {l : S.TILine // x ∈ l} = Nat.card (ℙ S.F K) * (S.q + 1) := by
    rw [Finset.sum_congr rfl (fun x _ => S.lines_on_pt x), Finset.sum_const, Finset.card_univ,
      Nat.card_eq_fintype_card, smul_eq_mul]
  have h3 : Nat.card S.TILine * (S.q + 1) = Nat.card (ℙ S.F K) * (S.q + 1) := by
    rw [← h1, ← h2]
    simp only [hP, hL]
    exact key
  rw [S.card_points] at h3
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos _) h3

/-- Corollary C1 for `W(3,q)`: the copy graph with `j` copies of the points of `O` (half each) and
`j` copies of the spread lines. -/
theorem corC1 {j : ℕ} (hj : Even j) (hj2 : 2 ≤ j) :
    ∃ H : SimpleGraph (Fin (2 * (S.q ^ 2 + 1) * (S.q + 1 + j))),
      IsBipartiteDegDiam H (S.q + 1 + j) 4 := by
  classical
  have hj2' : 2 * (j / 2) = j := Nat.two_mul_div_two_of_even hj
  let w : ℙ S.F K → ℕ := fun x => if S.Oz 0 x.rep then j / 2 else 0
  let m : S.TILine → ℕ := fun l => if S.IsSpread l then j else 0
  have hw : ∀ l : S.TILine, ∑ x ∈ Finset.univ.filter (fun x => x ∈ l), w x ≤ j := by
    intro l
    have hc : ((Finset.univ.filter (fun x => x ∈ l)).filter (fun x => S.Oz 0 x.rep)).card = 2 := by
      have h := S.card_O_line (Nat.zero_le _) l
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
      rw [Finset.filter_filter]
      convert h using 2
    have hs : ∑ x ∈ Finset.univ.filter (fun x => x ∈ l), w x =
        ∑ x ∈ (Finset.univ.filter (fun x => x ∈ l)).filter (fun x => S.Oz 0 x.rep), j / 2 := by
      symm
      rw [Finset.sum_filter]
    rw [hs, Finset.sum_const, hc, smul_eq_mul]
    omega
  have hm : ∀ x : ℙ S.F K, ∑ l ∈ Finset.univ.filter (fun l => x ∈ l), m l ≤ j := by
    intro x
    have hc : ((Finset.univ.filter (fun l : S.TILine => x ∈ l)).filter
        (fun l => S.IsSpread l)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact S.spread_unique ha.2 hb.2 ha.1 hb.1
    have hs : ∑ l ∈ Finset.univ.filter (fun l : S.TILine => x ∈ l), m l =
        ∑ l ∈ (Finset.univ.filter (fun l : S.TILine => x ∈ l)).filter (fun l => S.IsSpread l), j := by
      symm
      rw [Finset.sum_filter]
    rw [hs, Finset.sum_const, smul_eq_mul]
    exact le_trans (Nat.mul_le_mul_right j hc) (by simp)
  obtain ⟨H, hH⟩ := BipartiteDD.GQST.gqst S.gq_W w m j j hw hm
  rw [max_self] at hH
  have hP : Fintype.card (ℙ S.F K) = (S.q + 1) * (S.q ^ 2 + 1) := by
    rw [← Nat.card_eq_fintype_card, S.card_points]
  have hL : Fintype.card S.TILine = (S.q + 1) * (S.q ^ 2 + 1) := by
    rw [← Nat.card_eq_fintype_card, S.card_lines]
  have hW : ∑ x, w x = j * (S.q ^ 2 + 1) := by
    have hs : ∑ x, w x = ∑ x ∈ Finset.univ.filter (fun x : ℙ S.F K => S.Oz 0 x.rep), j / 2 := by
      rw [Finset.sum_filter]
    rw [hs, Finset.sum_const, smul_eq_mul]
    have hc : (Finset.univ.filter (fun x : ℙ S.F K => S.Oz 0 x.rep)).card = 2 * (S.q ^ 2 + 1) := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact S.card_O (Nat.zero_le _)
    rw [hc, show 2 * (S.q ^ 2 + 1) * (j / 2) = (S.q ^ 2 + 1) * (2 * (j / 2)) by ring, hj2']
    ring
  have hM : ∑ l, m l = j * (S.q ^ 2 + 1) := by
    have hs : ∑ l, m l = ∑ l ∈ Finset.univ.filter (fun l : S.TILine => S.IsSpread l), j := by
      rw [Finset.sum_filter]
    rw [hs, Finset.sum_const, smul_eq_mul]
    have hc : (Finset.univ.filter (fun l : S.TILine => S.IsSpread l)).card = S.q ^ 2 + 1 := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact S.card_spread
    rw [hc, mul_comm]
  have hn : Fintype.card (ℙ S.F K) + Fintype.card S.TILine + ∑ x, w x + ∑ l, m l =
      2 * (S.q ^ 2 + 1) * (S.q + 1 + j) := by
    rw [hP, hL, hW, hM]
    ring
  exact ⟨H.comap (finCongr hn).symm, isBipartiteDegDiam_comap (finCongr hn) hH⟩

/-- The case `j = 2`: `n_b(q + 3, 4) ≥ 2 (q² + 1)(q + 3)`. -/
theorem corC1_two :
    ∃ H : SimpleGraph (Fin (2 * (S.q ^ 2 + 1) * (S.q + 3))), IsBipartiteDegDiam H (S.q + 3) 4 := by
  obtain ⟨H, hH⟩ := S.corC1 (j := 2) even_two le_rfl
  have key : ∀ n n' d d' : ℕ, n = n' → d = d' → ∀ H : SimpleGraph (Fin n),
      IsBipartiteDegDiam H d 4 → ∃ H' : SimpleGraph (Fin n'), IsBipartiteDegDiam H' d' 4 := by
    rintro n n' d d' rfl rfl H h
    exact ⟨H, h⟩
  exact key _ _ _ _ (by ring) (by ring) H hH

end Setting

end BipartiteDD.SingerC

namespace BipartiteDD.SingerC

open scoped LinearAlgebra.Projectivization

variable {K : Type*} [Field K] [Fintype K] {p : ℕ} [Fact p.Prime] [CharP K p]

/-- `O_a`: the points of `W(3,q)` whose vectors lie in Singer class `a` or `q - a`. -/
def W3.O (S : Setting K p) (a : ℕ) : Set (ℙ S.F K) := {x | S.Oz a x.rep}

/-- Target 2, Proposition C: `O_a` is a 2-ovoid of `W(3,q)`: every line meets it in exactly two
points. -/
theorem propC (S : Setting K p) {a : ℕ} (ha : a ≤ S.q) (l : W3Line S) :
    Nat.card {x : ℙ S.F K // x ∈ l ∧ x ∈ W3.O S a} = 2 :=
  S.card_O_line ha l

/-- Target 4, Corollary C1. -/
theorem corC1 (S : Setting K p) {j : ℕ} (hj : Even j) (hj2 : 2 ≤ j) :
    ∃ H : SimpleGraph (Fin (2 * (S.q ^ 2 + 1) * (S.q + 1 + j))),
      IsBipartiteDegDiam H (S.q + 1 + j) 4 :=
  S.corC1 hj hj2

end BipartiteDD.SingerC
