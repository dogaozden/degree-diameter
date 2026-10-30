import BipartiteDD.Basic
import BipartiteDD.Fast
import BipartiteDD.Graphs.G384

/-! The (5,5) record on 384 vertices: a regular lift of the 4-vertex base `[[2,3],[3,2]]` by a group of order 96
(`research/beyond-haar-d5b/records/d5D5_n384_a1_g96_31.edges`, from the job beyond-haar-d5b), checked directly on its
neighbour lists by the kernel-friendly checker of `Fast`. -/

theorem nb_5_5_n384 : ∃ G : SimpleGraph (Fin 384), BipartiteDD.IsBipartiteDegDiam G 5 5 :=
  ⟨_, BipartiteDD.check_sound 5 5 BipartiteDD.G384.nbrs BipartiteDD.G384.color
    (BipartiteDD.Fast.check_of_fast 9 5 5 BipartiteDD.G384.adjL BipartiteDD.G384.colL
      (by decide) (by decide +kernel))⟩
