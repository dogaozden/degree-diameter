import BipartiteDD.GQST.StandinDiam
import BipartiteDD.GQST.StandinDegree
import BipartiteDD.GQ4.Main

/-! Group GQST, part 9: the main theorems for stand-ins (Theorem B of `research/NOTE.md`, Section 2).

`standin_isBipartiteDegDiam` is the stand-in graph of a generalized quadrangle of order `(s, t)`, with `w p` copies of
each point `p`, `m l` copies of each line `l`, and stand-ins `σ`. When every line has total point weight at most `a`
and each stand-in serves at most `b` line copies, the graph is bipartite, has maximum degree at most
`max (s + 1 + a) (t + 1 + b)` and diameter at most `4`. `standin_gqst` transports it to `Fin n`.

With every stand-in the original point, the graph is `blowup` (`standin_zero_eq_blowup`), so `GQST.isBipartiteDegDiam`
is the special case `σ = 0`. -/

namespace BipartiteDD.GQST

open SimpleGraph
open scoped Classical

variable {P L : Type*} [Membership P L]

/-- Group GQST, stand-ins: the main theorem. -/
theorem standin_isBipartiteDegDiam [Fintype P] [Fintype L] {s t : ℕ} (G : GQst P L s t) (w : P → ℕ)
    (m : L → ℕ) (σ : (c : Σ l, Fin (m l)) → (p : P) → p ∈ c.1 → Fin (w p + 1)) (a b : ℕ)
    (hw : ∀ l : L, ∑ p ∈ Finset.univ.filter (fun p => p ∈ l), w p ≤ a)
    (hσ : ∀ (p : P) (j : Fin (w p + 1)),
      (Finset.univ.filter (fun c : Σ l, Fin (m l) => ∃ hp : p ∈ c.1, σ c p hp = j)).card ≤ b) :
    IsBipartiteDegDiam (standin P L w m σ) (max (s + 1 + a) (t + 1 + b)) 4 :=
  ⟨standin_colorable σ, fun v => standin_degree G a b hw hσ v, by exact_mod_cast standin_ediam G⟩

/-- Group GQST, stand-ins, transported to `Fin n` with `n` the number of vertices of the stand-in graph. -/
theorem standin_gqst [Fintype P] [Fintype L] {s t : ℕ} (G : GQst P L s t) (w : P → ℕ) (m : L → ℕ)
    (σ : (c : Σ l, Fin (m l)) → (p : P) → p ∈ c.1 → Fin (w p + 1)) (a b : ℕ)
    (hw : ∀ l : L, ∑ p ∈ Finset.univ.filter (fun p => p ∈ l), w p ≤ a)
    (hσ : ∀ (p : P) (j : Fin (w p + 1)),
      (Finset.univ.filter (fun c : Σ l, Fin (m l) => ∃ hp : p ∈ c.1, σ c p hp = j)).card ≤ b) :
    ∃ H : SimpleGraph (Fin (Fintype.card P + Fintype.card L + ∑ p, w p + ∑ l, m l)),
      IsBipartiteDegDiam H (max (s + 1 + a) (t + 1 + b)) 4 := by
  have hcard : Fintype.card ((P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l))) =
      Fintype.card P + Fintype.card L + ∑ p, w p + ∑ l, m l := by
    simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
    ring
  let e := Fintype.equivFinOfCardEq hcard
  exact ⟨(standin P L w m σ).comap e.symm,
    isBipartiteDegDiam_comap e (standin_isBipartiteDegDiam G w m σ a b hw hσ)⟩

end BipartiteDD.GQST
