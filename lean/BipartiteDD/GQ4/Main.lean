import BipartiteDD.Basic
import BipartiteDD.GQ4.Degree
import Mathlib.Tactic.Linarith

/-! Group GQ4, part 6: the main theorems. `isBipartiteDegDiam` is the copy graph of a generalized
quadrangle with copies of an ovoid-like set `O` and of a line multiset `m`; `gq4` transports it to
`Fin n` along a bijection. -/

namespace BipartiteDD

open SimpleGraph
open scoped Classical

/-- A graph homomorphism maps walks to walks of the same length, so it does not increase distances. -/
theorem edist_le_of_hom {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'}
    (f : G →g G') (u v : V) : G'.edist (f u) (f v) ≤ G.edist u v := by
  by_cases h : G.edist u v = ⊤
  · rw [h]
    exact le_top
  · obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top h
    calc G'.edist (f u) (f v) ≤ ((p.map f).length : ℕ∞) := edist_le _
      _ = (p.length : ℕ∞) := by rw [Walk.length_map]
      _ = G.edist u v := hp

/-- The identity map from `H.comap e.symm` to `H`, read through `e`: an edge `x ~ y` of `H` gives an
edge `e x ~ e y` of `H.comap e.symm`. -/
def comapHom {V V' : Type*} (e : V ≃ V') (H : SimpleGraph V) : H →g H.comap e.symm where
  toFun := e
  map_rel' := fun {x y} h => by
    simp only [SimpleGraph.comap_adj, Equiv.symm_apply_apply]
    exact h

/-- Transport along a bijection: a graph with the bipartite, degree and diameter bounds keeps them. -/
theorem isBipartiteDegDiam_comap {V V' : Type*} {H : SimpleGraph V} {d D : ℕ} (e : V ≃ V')
    (hH : IsBipartiteDegDiam H d D) : IsBipartiteDegDiam (H.comap e.symm) d D := by
  refine ⟨Colorable.of_hom (SimpleGraph.Iso.comap e.symm H).toHom hH.1, fun v => ?_, ?_⟩
  · have hset : (H.comap e.symm).neighborSet v = e.symm ⁻¹' (H.neighborSet (e.symm v)) := by
      ext w
      exact Iff.rfl
    rw [hset, Set.ncard_preimage_of_injective_subset_range e.symm.injective
      (by rw [e.symm.surjective.range_eq]; exact Set.subset_univ _)]
    exact hH.2.1 _
  · rw [ediam_le_iff]
    intro u v
    have h := edist_le_of_hom (comapHom e H) (e.symm u) (e.symm v)
    have hu : comapHom e H (e.symm u) = u := e.apply_symm_apply u
    have hv : comapHom e H (e.symm v) = v := e.apply_symm_apply v
    rw [hu, hv] at h
    exact h.trans (edist_le_ediam.trans hH.2.2)

namespace GQ4

variable {P L : Type*} [Membership P L]

/-- Group GQ4, main theorem. For a generalized quadrangle `G` of order `(q, q)`, a set `O` of points
meeting every line in at most one point, and a multiset of lines given by `m` in which every point lies
on lines of total multiplicity at most `j`, the copy graph is bipartite, has maximum degree `q + 1 + j`
and diameter at most `4`. -/
theorem isBipartiteDegDiam [Fintype P] [Fintype L] {q : ℕ} (G : GQ P L q) (O : Finset P)
    (hO : ∀ l : L, (O.filter (fun p => p ∈ l)).card ≤ 1) (j : ℕ) (m : L → ℕ)
    (hm : ∀ p : P, ∑ l ∈ Finset.univ.filter (fun l => p ∈ l), m l ≤ j) :
    IsBipartiteDegDiam (blowup P L O j m) (q + 1 + j) 4 :=
  ⟨blowup_colorable O j m, fun v => blowup_degree G O hO j m hm v, by
    exact_mod_cast blowup_ediam G O j m⟩

/-- Group GQ4, transported to `Fin n` with `n` the number of vertices of the copy graph. -/
theorem gq4 [Fintype P] [Fintype L] {q : ℕ} (G : GQ P L q) (O : Finset P)
    (hO : ∀ l : L, (O.filter (fun p => p ∈ l)).card ≤ 1) (j : ℕ) (m : L → ℕ)
    (hm : ∀ p : P, ∑ l ∈ Finset.univ.filter (fun l => p ∈ l), m l ≤ j) :
    ∃ H : SimpleGraph (Fin (Fintype.card P + Fintype.card L + j * O.card + ∑ l, m l)),
      IsBipartiteDegDiam H (q + 1 + j) 4 := by
  have hcard : Fintype.card ((P ⊕ (O × Fin j)) ⊕ (L ⊕ Σ l, Fin (m l))) =
      Fintype.card P + Fintype.card L + j * O.card + ∑ l, m l := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma,
      Fintype.card_coe]
    ring
  let e := Fintype.equivFinOfCardEq hcard
  exact ⟨(blowup P L O j m).comap e.symm,
    isBipartiteDegDiam_comap e (isBipartiteDegDiam G O hO j m hm)⟩

end GQ4

end BipartiteDD
