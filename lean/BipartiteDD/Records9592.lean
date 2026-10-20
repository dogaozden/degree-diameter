import BipartiteDD.Basic
import BipartiteDD.Staged
import BipartiteDD.Graphs.G9592
import BipartiteDD.Graphs.G9592_levs
import BipartiteDD.Stages.G9592_local
import BipartiteDD.Stages.G9592_s0
import BipartiteDD.Stages.G9592_s1
import BipartiteDD.Stages.G9592_s2
import BipartiteDD.Stages.G9592_s3
import BipartiteDD.Stages.G9592_s4
import BipartiteDD.Stages.G9592_s5

theorem nb_7_6 : ∃ G : SimpleGraph (Fin 9592), BipartiteDD.IsBipartiteDegDiam G 7 6 :=
  ⟨_, BipartiteDD.check_sound 7 6 BipartiteDD.G9592.nbrs BipartiteDD.G9592.color
    (BipartiteDD.Staged.check_of_chain 14 7 6 BipartiteDD.G9592.adjL BipartiteDD.G9592.colL
      (by decide) BipartiteDD.G9592.levs (by decide) BipartiteDD.G9592.local_ok
      (by
        intro r hr
        obtain rfl | rfl | rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by omega
        exacts [BipartiteDD.G9592.stage0, BipartiteDD.G9592.stage1, BipartiteDD.G9592.stage2, BipartiteDD.G9592.stage3, BipartiteDD.G9592.stage4, BipartiteDD.G9592.stage5]))⟩
