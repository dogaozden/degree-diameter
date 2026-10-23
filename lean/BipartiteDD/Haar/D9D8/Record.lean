import BipartiteDD.Haar.D9D8.Covers
import BipartiteDD.Haar.D9D8.Even8

/-! The Δ9·D8 record: `497,904` vertices, degree `9`, diameter `8`, from the Haar graph of `PSL(2, 23) × Z41`
with the set `S` of `research/frontier/sols/d9D8_psl_23_41_s301.txt`. -/

namespace BipartiteDD.Haar.D9D8

open BipartiteDD.Haar

/-- The Haar graph of `SS`, transported to `Fin 497904`. -/
def G9D8 : SimpleGraph (Fin 497904) := (haarGraph SS).comap haarVert.symm

theorem isBipartiteDegDiam_G9D8 : BipartiteDD.IsBipartiteDegDiam G9D8 9 8 := by
  have h := isBipartiteDegDiam8_even_of SS G9D8 haarVert
    (fun x y => by simp [G9D8, SimpleGraph.comap_adj]) coverE
  rw [card_SS] at h
  exact h

end BipartiteDD.Haar.D9D8

open BipartiteDD.Haar.D9D8 in
/-- A bipartite graph on `497904` vertices with degree at most `9` and diameter at most `8`. -/
theorem nb_9_8 : ∃ H : SimpleGraph (Fin 497904), BipartiteDD.IsBipartiteDegDiam H 9 8 :=
  ⟨G9D8, isBipartiteDegDiam_G9D8⟩
