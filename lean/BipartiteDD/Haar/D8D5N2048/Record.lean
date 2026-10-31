import BipartiteDD.Basic
import BipartiteDD.Fast
import BipartiteDD.Staged
import BipartiteDD.Haar.D8D5N2048.Graph
import BipartiteDD.Haar.D8D5N2048.Levels
import BipartiteDD.Haar.D8D5N2048.Check
import BipartiteDD.Haar.D8D5N2048.Stage00
import BipartiteDD.Haar.D8D5N2048.Stage01
import BipartiteDD.Haar.D8D5N2048.Stage02
import BipartiteDD.Haar.D8D5N2048.Stage03
import BipartiteDD.Haar.D8D5N2048.Stage04

/-! The record, proved by the staged check: the ball masks of each radius are data (`Levels`), and each radius
step is checked in its own module (`Stage00 … Stage04`), so the kernel never holds the whole
computation (the one-shot `decide +kernel` of `Fast.checkFast` exceeds 12 GB here). The local test is `Check`. -/

open BipartiteDD in
/-- A graph on 2048 vertices, bipartite, of degree at most 8 and diameter at most 5. -/
theorem nb_8_5_n2048 : ∃ G : SimpleGraph (Fin 2048), BipartiteDD.IsBipartiteDegDiam G 8 5 :=
  ⟨_, BipartiteDD.check_sound 8 5 BipartiteDD.Haar.D8D5N2048.nbrs BipartiteDD.Haar.D8D5N2048.color
    (BipartiteDD.Staged.check_of_chain 11 8 5 BipartiteDD.Haar.D8D5N2048.adjL BipartiteDD.Haar.D8D5N2048.colL
      (by decide) BipartiteDD.Haar.D8D5N2048.levs (by decide) BipartiteDD.Haar.D8D5N2048.local_ok
      (by
        intro r hr
        obtain rfl | rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
        exacts [BipartiteDD.Haar.D8D5N2048.stage00, BipartiteDD.Haar.D8D5N2048.stage01, BipartiteDD.Haar.D8D5N2048.stage02, BipartiteDD.Haar.D8D5N2048.stage03, BipartiteDD.Haar.D8D5N2048.stage04]))⟩
