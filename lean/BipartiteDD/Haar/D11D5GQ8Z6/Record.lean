import BipartiteDD.Basic
import BipartiteDD.Fast
import BipartiteDD.Staged
import BipartiteDD.Haar.D11D5GQ8Z6.Graph
import BipartiteDD.Haar.D11D5GQ8Z6.Levels
import BipartiteDD.Haar.D11D5GQ8Z6.Check
import BipartiteDD.Haar.D11D5GQ8Z6.Stage00
import BipartiteDD.Haar.D11D5GQ8Z6.Stage01
import BipartiteDD.Haar.D11D5GQ8Z6.Stage02
import BipartiteDD.Haar.D11D5GQ8Z6.Stage03
import BipartiteDD.Haar.D11D5GQ8Z6.Stage04

/-! The record, proved by the staged check: the ball masks of each radius are data (`Levels`), and each radius
step is checked in its own module (`Stage00 … Stage04`), so the kernel never holds the whole
computation (the one-shot `decide +kernel` of `Fast.checkFast` exceeds 12 GB here). The local test is `Check`. -/

open BipartiteDD in
/-- A graph on 7020 vertices, bipartite, of degree at most 11 and diameter at most 5. -/
theorem nb_11_5_n7020 : ∃ G : SimpleGraph (Fin 7020), BipartiteDD.IsBipartiteDegDiam G 11 5 :=
  ⟨_, BipartiteDD.check_sound 11 5 BipartiteDD.Haar.D11D5GQ8Z6.nbrs BipartiteDD.Haar.D11D5GQ8Z6.color
    (BipartiteDD.Staged.check_of_chain 13 11 5 BipartiteDD.Haar.D11D5GQ8Z6.adjL BipartiteDD.Haar.D11D5GQ8Z6.colL
      (by decide) BipartiteDD.Haar.D11D5GQ8Z6.levs (by decide) BipartiteDD.Haar.D11D5GQ8Z6.local_ok
      (by
        intro r hr
        obtain rfl | rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
        exacts [BipartiteDD.Haar.D11D5GQ8Z6.stage00, BipartiteDD.Haar.D11D5GQ8Z6.stage01, BipartiteDD.Haar.D11D5GQ8Z6.stage02, BipartiteDD.Haar.D11D5GQ8Z6.stage03, BipartiteDD.Haar.D11D5GQ8Z6.stage04]))⟩
