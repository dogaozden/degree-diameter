import BipartiteDD.Haar.D9D8b.Covers
import BipartiteDD.Haar.D9D8.Even8

/-! The Δ9·D8 record: `511,056` vertices, degree `9`, diameter `8`, from the Haar graph of `SL(2, 27) × Z13`
with the set `S` of `research/frontier/sols/d9D8_sl_27_13_orb3_s1.txt`. The diameter-8 lemma
`ediam_le_eight_even_of` is the one of the `D9D8` record (`BipartiteDD.Haar.D9D8.Even8`). -/

namespace BipartiteDD.Haar.D9D8b

open BipartiteDD.Haar

/-- The Haar graph of `SS`, transported to `Fin 511056`. -/
def G9D8b : SimpleGraph (Fin 511056) := (haarGraph SS).comap haarVert.symm

theorem isBipartiteDegDiam_G9D8b : BipartiteDD.IsBipartiteDegDiam G9D8b 9 8 := by
  have h := isBipartiteDegDiam8_even_of SS G9D8b haarVert
    (fun x y => by simp [G9D8b, SimpleGraph.comap_adj]) coverE
  rw [card_SS] at h
  exact h

end BipartiteDD.Haar.D9D8b

open BipartiteDD.Haar.D9D8b in
/-- A bipartite graph on `511056` vertices with degree at most `9` and diameter at most `8`. -/
theorem nb_9_8_511056 : ∃ H : SimpleGraph (Fin 511056), BipartiteDD.IsBipartiteDegDiam H 9 8 :=
  ⟨G9D8b, isBipartiteDegDiam_G9D8b⟩
