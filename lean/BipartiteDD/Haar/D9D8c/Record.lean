import BipartiteDD.Haar.D9D8c.Covers
import BipartiteDD.Haar.D9D8.Even8

/-! The Δ9·D8 record `540,360`: degree `9`, diameter `8`, from the Haar graph of `PSL(2, 19) × Z79` with the set `S`
of `research/frontier/sols/d9D8_psl_19_79_orb3_s1.txt`. The diameter-8 lemma `isBipartiteDegDiam8_even_of` is the
one of the `497,904` record (`Haar.D9D8.Even8`), which is generic in the group. -/

namespace BipartiteDD.Haar.D9D8c

open BipartiteDD.Haar

/-- The Haar graph of `SS`, transported to `Fin 540360`. -/
def G9D8c : SimpleGraph (Fin 540360) := (haarGraph SS).comap haarVert.symm

theorem isBipartiteDegDiam_G9D8c : BipartiteDD.IsBipartiteDegDiam G9D8c 9 8 := by
  have h := isBipartiteDegDiam8_even_of SS G9D8c haarVert
    (fun x y => by simp [G9D8c, SimpleGraph.comap_adj]) coverE
  rw [card_SS] at h
  exact h

end BipartiteDD.Haar.D9D8c

open BipartiteDD.Haar.D9D8c in
/-- A bipartite graph on `540360` vertices with degree at most `9` and diameter at most `8`. -/
theorem nb_9_8_540360 : ∃ H : SimpleGraph (Fin 540360), BipartiteDD.IsBipartiteDegDiam H 9 8 :=
  ⟨G9D8c, isBipartiteDegDiam_G9D8c⟩
