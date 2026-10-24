import BipartiteDD.Basic
import BipartiteDD.Fast
import BipartiteDD.Haar.LiftD.Formula288

/-! The (3,8) record on 288 vertices: the voltage lift of a 4-vertex cubic base graph over `Z3^2 x|_M Z8`
(`BipartiteDD.LiftD.Formula288`, voltages from `research/lifts/sols/c1r_d3D8_n288_b2_3_0_aff302108_s1.txt`).
The check is `Fast.checkFast` (a kernel-friendly `check`), evaluated by `decide +kernel`. -/

open BipartiteDD in
/-- A graph on 288 vertices, bipartite, of degree at most 3 and diameter at most 8. -/
theorem nb_3_8_288 : ∃ G : SimpleGraph (Fin 288), BipartiteDD.IsBipartiteDegDiam G 3 8 :=
  ⟨_, check_sound 3 8 (fun u : Fin 288 => LiftD.adjL.getD u.val [])
    (fun u : Fin 288 => LiftD.colL.getD u.val false)
    (Fast.check_of_fast 9 3 8 LiftD.adjL LiftD.colL (by decide) (by decide +kernel))⟩
