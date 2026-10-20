import BipartiteDD.Doubling.Single
import BipartiteDD.Doubling.Theorem1
import BipartiteDD.Doubling.Hat

/-! Group Doubling, part 7: doubling the incidence graph of a generalized `n`-gon. Lemma 2 (the hat
lemma) provides the diameter condition (c) with `D = n` from the shape of `G[A₀]`; the doubling theorems
then give bipartite graphs of diameter at most `n` and degree at most `Δ + 1` (one level) or `Δ + m - 1`
(levels). -/

namespace BipartiteDD.Doubling

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {A : Set V}

/-- Single-level doubling of a generalized `n`-gon: if each vertex outside `A` has at most one neighbour
in `A` and every component of `G[A]` is a tree of diameter at most `n - 2`, the doubling is bipartite of
degree at most `Δ + 1` and diameter at most `n`. -/
theorem isBipartiteDegDiam_double_polygon [Finite V] {n Δ : ℕ} (hG : GenPolygonGraph G n)
    (hΔ : ∀ v, (G.neighborSet v).ncard ≤ Δ) (hb : ∀ v, v ∉ A → (G.neighborSet v ∩ A).ncard ≤ 1)
    (hF : ForestDiam G A (n - 2)) : IsBipartiteDegDiam (double G A) (Δ + 1) n :=
  isBipartiteDegDiam_double ⟨hG.colorable, hΔ, hG.ediam.le⟩ hb (hG.condC_of_forestDiam hF)

/-- Levelled doubling of a generalized `n`-gon along levels `A 0 ⊇ A 1 ⊇ …`: Theorem 1 with (c) supplied
by Lemma 2, when every component of `G[A 0]` is a tree of diameter at most `n - 2`. -/
theorem delorme_levelled_polygon [Fintype V] {n Δ m : ℕ} (hm : 0 < m) (hG : GenPolygonGraph G n)
    (hΔ : ∀ v, (G.neighborSet v).ncard ≤ Δ) {A : ℕ → Set V} (hA : Antitone A) {K : ℕ} (hK : A K = ∅)
    (ha1 : ∀ i, ∀ v ∈ A (i + 1), ∀ u, G.Adj u v → u ∈ A i)
    (ha2 : ∀ i, ∀ u ∈ A i, u ∉ A (i + 1) → (G.neighborSet u ∩ A (i + 1)).ncard ≤ 1)
    (hb : ∀ u, u ∉ A 0 → (G.neighborSet u ∩ A 0).ncard ≤ 1) (hF : ForestDiam G (A 0) (n - 2)) :
    ∃ H : SimpleGraph (Fin (Nat.card V + (m - 1) * ∑ i ∈ Finset.range K, m ^ i * (A i).ncard)),
      IsBipartiteDegDiam H (Δ + (m - 1)) n :=
  delorme_levelled hm ⟨hG.colorable, hΔ, hG.ediam.le⟩ hA hK ha1 ha2 hb (hG.condC_of_forestDiam hF)

end BipartiteDD.Doubling
