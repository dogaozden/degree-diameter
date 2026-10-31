import BipartiteDD.Basic
import BipartiteDD.Fast
import BipartiteDD.Staged
import BipartiteDD.Haar.D3D12N2368.Graph
import BipartiteDD.Haar.D3D12N2368.Levels
import BipartiteDD.Haar.D3D12N2368.Check
import BipartiteDD.Haar.D3D12N2368.Stage00
import BipartiteDD.Haar.D3D12N2368.Stage01
import BipartiteDD.Haar.D3D12N2368.Stage02
import BipartiteDD.Haar.D3D12N2368.Stage03
import BipartiteDD.Haar.D3D12N2368.Stage04
import BipartiteDD.Haar.D3D12N2368.Stage05
import BipartiteDD.Haar.D3D12N2368.Stage06
import BipartiteDD.Haar.D3D12N2368.Stage07
import BipartiteDD.Haar.D3D12N2368.Stage08
import BipartiteDD.Haar.D3D12N2368.Stage09
import BipartiteDD.Haar.D3D12N2368.Stage10
import BipartiteDD.Haar.D3D12N2368.Stage11

/-! The record, proved by the staged check: the ball masks of each radius are data (`Levels`), and each radius
step is checked in its own module (`Stage00 … Stage11`), so the kernel never holds the whole
computation (the one-shot `decide +kernel` of `Fast.checkFast` exceeds 12 GB here). The local test is `Check`. -/

open BipartiteDD in
/-- A graph on 2368 vertices, bipartite, of degree at most 3 and diameter at most 12. -/
theorem nb_3_12_2368 : ∃ G : SimpleGraph (Fin 2368), BipartiteDD.IsBipartiteDegDiam G 3 12 :=
  ⟨_, BipartiteDD.check_sound 3 12 BipartiteDD.Haar.D3D12N2368.nbrs BipartiteDD.Haar.D3D12N2368.color
    (BipartiteDD.Staged.check_of_chain 12 3 12 BipartiteDD.Haar.D3D12N2368.adjL BipartiteDD.Haar.D3D12N2368.colL
      (by decide) BipartiteDD.Haar.D3D12N2368.levs (by decide) BipartiteDD.Haar.D3D12N2368.local_ok
      (by
        intro r hr
        obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 := by omega
        exacts [BipartiteDD.Haar.D3D12N2368.stage00, BipartiteDD.Haar.D3D12N2368.stage01, BipartiteDD.Haar.D3D12N2368.stage02, BipartiteDD.Haar.D3D12N2368.stage03, BipartiteDD.Haar.D3D12N2368.stage04, BipartiteDD.Haar.D3D12N2368.stage05, BipartiteDD.Haar.D3D12N2368.stage06, BipartiteDD.Haar.D3D12N2368.stage07, BipartiteDD.Haar.D3D12N2368.stage08, BipartiteDD.Haar.D3D12N2368.stage09, BipartiteDD.Haar.D3D12N2368.stage10, BipartiteDD.Haar.D3D12N2368.stage11]))⟩
