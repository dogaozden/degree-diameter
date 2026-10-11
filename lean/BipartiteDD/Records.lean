import BipartiteDD.Basic
import BipartiteDD.Fast
import BipartiteDD.Graphs.G162
import BipartiteDD.Graphs.G344
import BipartiteDD.Graphs.G356
import BipartiteDD.Graphs.G192
import BipartiteDD.Graphs.G276
import BipartiteDD.Graphs.G1773

theorem nb_4_5 : ∃ G : SimpleGraph (Fin 162), BipartiteDD.IsBipartiteDegDiam G 4 5 :=
  ⟨_, BipartiteDD.check_sound 4 5 BipartiteDD.G162.nbrs BipartiteDD.G162.color
    (BipartiteDD.Fast.check_of_fast 8 4 5 BipartiteDD.G162.adjL BipartiteDD.G162.colL
      (by decide) (by decide +kernel))⟩

theorem nb_5_5 : ∃ G : SimpleGraph (Fin 344), BipartiteDD.IsBipartiteDegDiam G 5 5 :=
  ⟨_, BipartiteDD.check_sound 5 5 BipartiteDD.G344.nbrs BipartiteDD.G344.color
    (BipartiteDD.Fast.check_of_fast 9 5 5 BipartiteDD.G344.adjL BipartiteDD.G344.colL
      (by decide) (by decide +kernel))⟩

theorem nb_7_4 : ∃ G : SimpleGraph (Fin 356), BipartiteDD.IsBipartiteDegDiam G 7 4 :=
  ⟨_, BipartiteDD.check_sound 7 4 BipartiteDD.G356.nbrs BipartiteDD.G356.color
    (BipartiteDD.Fast.check_of_fast 9 7 4 BipartiteDD.G356.adjL BipartiteDD.G356.colL
      (by decide) (by decide +kernel))⟩

theorem nb_11_3 : ∃ G : SimpleGraph (Fin 192), BipartiteDD.IsBipartiteDegDiam G 11 3 :=
  ⟨_, BipartiteDD.check_sound 11 3 BipartiteDD.G192.nbrs BipartiteDD.G192.color
    (BipartiteDD.Fast.check_of_fast 8 11 3 BipartiteDD.G192.adjL BipartiteDD.G192.colL
      (by decide) (by decide +kernel))⟩

theorem nb_13_3 : ∃ G : SimpleGraph (Fin 276), BipartiteDD.IsBipartiteDegDiam G 13 3 :=
  ⟨_, BipartiteDD.check_sound 13 3 BipartiteDD.G276.nbrs BipartiteDD.G276.color
    (BipartiteDD.Fast.check_of_fast 9 13 3 BipartiteDD.G276.adjL BipartiteDD.G276.colL
      (by decide) (by decide +kernel))⟩

theorem nb_11_4 : ∃ G : SimpleGraph (Fin 1773), BipartiteDD.IsBipartiteDegDiam G 11 4 :=
  ⟨_, BipartiteDD.check_sound 11 4 BipartiteDD.G1773.nbrs BipartiteDD.G1773.color
    (BipartiteDD.Fast.check_of_fast 11 11 4 BipartiteDD.G1773.adjL BipartiteDD.G1773.colL
      (by decide) (by decide +kernel))⟩
