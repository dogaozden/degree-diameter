import BipartiteDD.Basic
import BipartiteDD.Fast
import BipartiteDD.Graphs.G162
import BipartiteDD.Graphs.G354
import BipartiteDD.Graphs.G1140
import BipartiteDD.Graphs.G359
import BipartiteDD.Graphs.G1774
import BipartiteDD.Graphs.G192
import BipartiteDD.Graphs.G276
import BipartiteDD.Graphs.G376
import BipartiteDD.Graphs.G396
import BipartiteDD.Staged
import BipartiteDD.Graphs.G2510
import BipartiteDD.Graphs.G3122
import BipartiteDD.Stages.G2510_local
import BipartiteDD.Stages.G2510_s0
import BipartiteDD.Stages.G2510_s1
import BipartiteDD.Stages.G2510_s2
import BipartiteDD.Stages.G2510_s3
import BipartiteDD.Stages.G2510_s4
import BipartiteDD.Stages.G3122_local
import BipartiteDD.Stages.G3122_s0
import BipartiteDD.Stages.G3122_s1
import BipartiteDD.Stages.G3122_s2
import BipartiteDD.Stages.G3122_s3
import BipartiteDD.Graphs.G1782
import BipartiteDD.Graphs.G3146
import BipartiteDD.Stages.G1782_local
import BipartiteDD.Stages.G1782_s0
import BipartiteDD.Stages.G1782_s1
import BipartiteDD.Stages.G1782_s2
import BipartiteDD.Stages.G1782_s3
import BipartiteDD.Stages.G3146_local
import BipartiteDD.Stages.G3146_s0
import BipartiteDD.Stages.G3146_s1
import BipartiteDD.Stages.G3146_s2
import BipartiteDD.Stages.G3146_s3
import BipartiteDD.Graphs.G5070
import BipartiteDD.Stages.G5070_local
import BipartiteDD.Stages.G5070_s0
import BipartiteDD.Stages.G5070_s1
import BipartiteDD.Stages.G5070_s2
import BipartiteDD.Stages.G5070_s3
import BipartiteDD.Graphs.G5440
import BipartiteDD.Stages.G5440_local
import BipartiteDD.Stages.G5440_s0
import BipartiteDD.Stages.G5440_s1
import BipartiteDD.Stages.G5440_s2
import BipartiteDD.Stages.G5440_s3

theorem nb_4_5 : ∃ G : SimpleGraph (Fin 162), BipartiteDD.IsBipartiteDegDiam G 4 5 :=
  ⟨_, BipartiteDD.check_sound 4 5 BipartiteDD.G162.nbrs BipartiteDD.G162.color
    (BipartiteDD.Fast.check_of_fast 8 4 5 BipartiteDD.G162.adjL BipartiteDD.G162.colL
      (by decide) (by decide +kernel))⟩

theorem nb_5_5 : ∃ G : SimpleGraph (Fin 354), BipartiteDD.IsBipartiteDegDiam G 5 5 :=
  ⟨_, BipartiteDD.check_sound 5 5 BipartiteDD.G354.nbrs BipartiteDD.G354.color
    (BipartiteDD.Fast.check_of_fast 9 5 5 BipartiteDD.G354.adjL BipartiteDD.G354.colL
      (by decide) (by decide +kernel))⟩

theorem nb_7_5 : ∃ G : SimpleGraph (Fin 1140), BipartiteDD.IsBipartiteDegDiam G 7 5 :=
  ⟨_, BipartiteDD.check_sound 7 5 BipartiteDD.G1140.nbrs BipartiteDD.G1140.color
    (BipartiteDD.Fast.check_of_fast 11 7 5 BipartiteDD.G1140.adjL BipartiteDD.G1140.colL
      (by decide) (by decide +kernel))⟩

theorem nb_7_4 : ∃ G : SimpleGraph (Fin 359), BipartiteDD.IsBipartiteDegDiam G 7 4 :=
  ⟨_, BipartiteDD.check_sound 7 4 BipartiteDD.G359.nbrs BipartiteDD.G359.color
    (BipartiteDD.Fast.check_of_fast 9 7 4 BipartiteDD.G359.adjL BipartiteDD.G359.colL
      (by decide) (by decide +kernel))⟩

theorem nb_11_4 : ∃ G : SimpleGraph (Fin 1774), BipartiteDD.IsBipartiteDegDiam G 11 4 :=
  ⟨_, BipartiteDD.check_sound 11 4 BipartiteDD.G1774.nbrs BipartiteDD.G1774.color
    (BipartiteDD.Fast.check_of_fast 11 11 4 BipartiteDD.G1774.adjL BipartiteDD.G1774.colL
      (by decide) (by decide +kernel))⟩

theorem nb_11_3 : ∃ G : SimpleGraph (Fin 192), BipartiteDD.IsBipartiteDegDiam G 11 3 :=
  ⟨_, BipartiteDD.check_sound 11 3 BipartiteDD.G192.nbrs BipartiteDD.G192.color
    (BipartiteDD.Fast.check_of_fast 8 11 3 BipartiteDD.G192.adjL BipartiteDD.G192.colL
      (by decide) (by decide +kernel))⟩

theorem nb_13_3 : ∃ G : SimpleGraph (Fin 276), BipartiteDD.IsBipartiteDegDiam G 13 3 :=
  ⟨_, BipartiteDD.check_sound 13 3 BipartiteDD.G276.nbrs BipartiteDD.G276.color
    (BipartiteDD.Fast.check_of_fast 9 13 3 BipartiteDD.G276.adjL BipartiteDD.G276.colL
      (by decide) (by decide +kernel))⟩

theorem nb_15_3 : ∃ G : SimpleGraph (Fin 376), BipartiteDD.IsBipartiteDegDiam G 15 3 :=
  ⟨_, BipartiteDD.check_sound 15 3 BipartiteDD.G376.nbrs BipartiteDD.G376.color
    (BipartiteDD.Fast.check_of_fast 9 15 3 BipartiteDD.G376.adjL BipartiteDD.G376.colL
      (by decide) (by decide +kernel))⟩

theorem nb_9_5 : ∃ G : SimpleGraph (Fin 2510), BipartiteDD.IsBipartiteDegDiam G 9 5 :=
  ⟨_, BipartiteDD.check_sound 9 5 BipartiteDD.G2510.nbrs BipartiteDD.G2510.color
    (BipartiteDD.Staged.check_of_chain 12 9 5 BipartiteDD.G2510.adjL BipartiteDD.G2510.colL
      (by decide) BipartiteDD.G2510.levs (by decide) BipartiteDD.G2510.local_ok
      (by
        intro r hr
        obtain rfl | rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
        exacts [BipartiteDD.G2510.stage0, BipartiteDD.G2510.stage1, BipartiteDD.G2510.stage2, BipartiteDD.G2510.stage3, BipartiteDD.G2510.stage4]))⟩

theorem nb_13_4 : ∃ G : SimpleGraph (Fin 3122), BipartiteDD.IsBipartiteDegDiam G 13 4 :=
  ⟨_, BipartiteDD.check_sound 13 4 BipartiteDD.G3122.nbrs BipartiteDD.G3122.color
    (BipartiteDD.Staged.check_of_chain 12 13 4 BipartiteDD.G3122.adjL BipartiteDD.G3122.colL
      (by decide) BipartiteDD.G3122.levs (by decide) BipartiteDD.G3122.local_ok
      (by
        intro r hr
        obtain rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
        exacts [BipartiteDD.G3122.stage0, BipartiteDD.G3122.stage1, BipartiteDD.G3122.stage2, BipartiteDD.G3122.stage3]))⟩

theorem nb_11_4_v2 : ∃ G : SimpleGraph (Fin 1782), BipartiteDD.IsBipartiteDegDiam G 11 4 :=
  ⟨_, BipartiteDD.check_sound 11 4 BipartiteDD.G1782.nbrs BipartiteDD.G1782.color
    (BipartiteDD.Staged.check_of_chain 11 11 4 BipartiteDD.G1782.adjL BipartiteDD.G1782.colL
      (by decide) BipartiteDD.G1782.levs (by decide) BipartiteDD.G1782.local_ok
      (by
        intro r hr
        obtain rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
        exacts [BipartiteDD.G1782.stage0, BipartiteDD.G1782.stage1, BipartiteDD.G1782.stage2, BipartiteDD.G1782.stage3]))⟩

theorem nb_13_4_v2 : ∃ G : SimpleGraph (Fin 3146), BipartiteDD.IsBipartiteDegDiam G 13 4 :=
  ⟨_, BipartiteDD.check_sound 13 4 BipartiteDD.G3146.nbrs BipartiteDD.G3146.color
    (BipartiteDD.Staged.check_of_chain 12 13 4 BipartiteDD.G3146.adjL BipartiteDD.G3146.colL
      (by decide) BipartiteDD.G3146.levs (by decide) BipartiteDD.G3146.local_ok
      (by
        intro r hr
        obtain rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
        exacts [BipartiteDD.G3146.stage0, BipartiteDD.G3146.stage1, BipartiteDD.G3146.stage2, BipartiteDD.G3146.stage3]))⟩

theorem nb_15_4_v2 : ∃ G : SimpleGraph (Fin 5070), BipartiteDD.IsBipartiteDegDiam G 15 4 :=
  ⟨_, BipartiteDD.check_sound 15 4 BipartiteDD.G5070.nbrs BipartiteDD.G5070.color
    (BipartiteDD.Staged.check_of_chain 13 15 4 BipartiteDD.G5070.adjL BipartiteDD.G5070.colL
      (by decide) BipartiteDD.G5070.levs (by decide) BipartiteDD.G5070.local_ok
      (by
        intro r hr
        obtain rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
        exacts [BipartiteDD.G5070.stage0, BipartiteDD.G5070.stage1, BipartiteDD.G5070.stage2, BipartiteDD.G5070.stage3]))⟩

theorem nb_16_4_v2 : ∃ G : SimpleGraph (Fin 5440), BipartiteDD.IsBipartiteDegDiam G 16 4 :=
  ⟨_, BipartiteDD.check_sound 16 4 BipartiteDD.G5440.nbrs BipartiteDD.G5440.color
    (BipartiteDD.Staged.check_of_chain 13 16 4 BipartiteDD.G5440.adjL BipartiteDD.G5440.colL
      (by decide) BipartiteDD.G5440.levs (by decide) BipartiteDD.G5440.local_ok
      (by
        intro r hr
        obtain rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
        exacts [BipartiteDD.G5440.stage0, BipartiteDD.G5440.stage1, BipartiteDD.G5440.stage2, BipartiteDD.G5440.stage3]))⟩

theorem nb_16_3 : ∃ G : SimpleGraph (Fin 396), BipartiteDD.IsBipartiteDegDiam G 16 3 :=
  ⟨_, BipartiteDD.check_sound 16 3 BipartiteDD.G396.nbrs BipartiteDD.G396.color
    (BipartiteDD.Fast.check_of_fast 9 16 3 BipartiteDD.G396.adjL BipartiteDD.G396.colL
      (by decide) (by decide +kernel))⟩
