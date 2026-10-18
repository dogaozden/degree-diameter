import BipartiteDD.GQST.Degree
import BipartiteDD.GQ4.Main

/-! Group GQST, part 5: the main theorems.

`GQST.isBipartiteDegDiam` is the weighted copy graph of a generalized quadrangle of order `(s, t)`, with
`w p` copies of each point `p` and `m l` copies of each line `l`, when every line carries total point
weight at most `a` and every point lies on lines of total line weight at most `b`. It is bipartite, has
maximum degree at most `max (s + 1 + a) (t + 1 + b)` and diameter at most `4`. `GQST.gqst` transports it
to `Fin n`.

The old theorem `GQ4.gq4` is the special case `s = t = q`, `w = j · 1_O`, `a = b = j`
(`GQST.gq4_of_gqst`). -/

namespace BipartiteDD

/-- A generalized quadrangle of order `(q, q)` is one of order `(q, q)` in the `GQst` sense. -/
theorem GQ.toGQst {P L : Type*} [Membership P L] {q : ℕ} (G : GQ P L q) : GQst P L q q :=
  ⟨G.pts_on_line, G.lines_on_pt, G.one_line, G.gq_ax⟩

namespace GQST

open SimpleGraph
open scoped Classical

variable {P L : Type*} [Membership P L]

/-- Group GQST, main theorem. For a generalized quadrangle `G` of order `(s, t)` with `w p` copies of
each point `p` and `m l` copies of each line `l`, where every line has total point weight at most `a`
and every point has total line weight at most `b`, the copy graph is bipartite, has maximum degree at
most `max (s + 1 + a) (t + 1 + b)` and diameter at most `4`. -/
theorem isBipartiteDegDiam [Fintype P] [Fintype L] {s t : ℕ} (G : GQst P L s t) (w : P → ℕ)
    (m : L → ℕ) (a b : ℕ)
    (hw : ∀ l : L, ∑ p ∈ Finset.univ.filter (fun p => p ∈ l), w p ≤ a)
    (hm : ∀ p : P, ∑ l ∈ Finset.univ.filter (fun l => p ∈ l), m l ≤ b) :
    IsBipartiteDegDiam (blowup P L w m) (max (s + 1 + a) (t + 1 + b)) 4 :=
  ⟨blowup_colorable w m, blowup_degree G w m a b hw hm, by
    exact_mod_cast blowup_ediam G w m⟩

/-- Group GQST, transported to `Fin n` with `n` the number of vertices of the copy graph. -/
theorem gqst [Fintype P] [Fintype L] {s t : ℕ} (G : GQst P L s t) (w : P → ℕ) (m : L → ℕ)
    (a b : ℕ)
    (hw : ∀ l : L, ∑ p ∈ Finset.univ.filter (fun p => p ∈ l), w p ≤ a)
    (hm : ∀ p : P, ∑ l ∈ Finset.univ.filter (fun l => p ∈ l), m l ≤ b) :
    ∃ H : SimpleGraph (Fin (Fintype.card P + Fintype.card L + ∑ p, w p + ∑ l, m l)),
      IsBipartiteDegDiam H (max (s + 1 + a) (t + 1 + b)) 4 := by
  have hcard : Fintype.card ((P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l))) =
      Fintype.card P + Fintype.card L + ∑ p, w p + ∑ l, m l := by
    simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
    ring
  let e := Fintype.equivFinOfCardEq hcard
  exact ⟨(blowup P L w m).comap e.symm,
    isBipartiteDegDiam_comap e (isBipartiteDegDiam G w m a b hw hm)⟩

/-- The old theorem `GQ4.gq4` as a special case: `j` copies of each point of `O` and `m l` copies of
each line `l`, with `s = t = q`, `a = b = j`. -/
theorem gq4_of_gqst [Fintype P] [Fintype L] {q : ℕ} (G : GQ P L q) (O : Finset P)
    (hO : ∀ l : L, (O.filter (fun p => p ∈ l)).card ≤ 1) (j : ℕ) (m : L → ℕ)
    (hm : ∀ p : P, ∑ l ∈ Finset.univ.filter (fun l => p ∈ l), m l ≤ j) :
    ∃ H : SimpleGraph (Fin (Fintype.card P + Fintype.card L + j * O.card + ∑ l, m l)),
      IsBipartiteDegDiam H (q + 1 + j) 4 := by
  let w : P → ℕ := fun p => if p ∈ O then j else 0
  have hsub : ∀ l : L, (Finset.univ.filter (fun p => p ∈ l)).filter (fun p => p ∈ O) =
      O.filter (fun p => p ∈ l) := by
    intro l
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hw : ∀ l : L, ∑ p ∈ Finset.univ.filter (fun p => p ∈ l), w p ≤ j := by
    intro l
    have hsum : ∑ p ∈ Finset.univ.filter (fun p => p ∈ l), w p =
        ((Finset.univ.filter (fun p => p ∈ l)).filter (fun p => p ∈ O)).card * j := by
      simp only [w]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
    rw [hsum, hsub l]
    calc (O.filter (fun p => p ∈ l)).card * j ≤ 1 * j := Nat.mul_le_mul_right j (hO l)
      _ = j := one_mul j
  have hsumw : ∑ p, w p = j * O.card := by
    have hO' : Finset.univ.filter (fun p => p ∈ O) = O := by
      ext x
      simp
    simp only [w]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, hO',
      mul_comm]
  obtain ⟨H, hH⟩ := gqst G.toGQst w m j j hw hm
  have hn : Fintype.card P + Fintype.card L + ∑ p, w p + ∑ l, m l =
      Fintype.card P + Fintype.card L + j * O.card + ∑ l, m l := by
    rw [hsumw]
  rw [max_self] at hH
  exact ⟨H.comap (finCongr hn).symm, isBipartiteDegDiam_comap (finCongr hn) hH⟩

end GQST

end BipartiteDD
