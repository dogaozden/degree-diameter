import BipartiteDD.Basic
import BipartiteDD.Fast
import BipartiteDD.Graphs.G360

/-! The (5,5) record on 360 vertices: a regular lift of the 4-vertex base `[[2,3],[3,2]]` by `Z_15 × S_3`
(`research/beyond-haar-d5/records/build_d5D5_n360_z15s3.py`), checked directly on its neighbour lists
by the kernel-friendly checker of `Fast`. -/

theorem nb_5_5_n360 : ∃ G : SimpleGraph (Fin 360), BipartiteDD.IsBipartiteDegDiam G 5 5 :=
  ⟨_, BipartiteDD.check_sound 5 5 BipartiteDD.G360.nbrs BipartiteDD.G360.color
    (BipartiteDD.Fast.check_of_fast 9 5 5 BipartiteDD.G360.adjL BipartiteDD.G360.colL
      (by decide) (by decide +kernel))⟩
