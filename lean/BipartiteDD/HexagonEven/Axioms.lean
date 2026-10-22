import BipartiteDD.HexagonEven.Main
import BipartiteDD.HexagonEven.Sanity
import BipartiteDD.HexagonEven.Pi
import BipartiteDD.HexagonEven.PiCount
import BipartiteDD.HexagonEven.Identity
import BipartiteDD.HexagonEven.JLine
import BipartiteDD.HexagonEven.KeyId
import BipartiteDD.HexagonEven.GCubic
import BipartiteDD.HexagonEven.PiZ
import BipartiteDD.HexagonEven.ExactW
import BipartiteDD.HexagonEven.ThmD
import BipartiteDD.HexagonEven.Reg.Final
import BipartiteDD.HexagonEven.Spread
import BipartiteDD.HexagonEven.Levels
import BipartiteDD.HexagonEven.LevelsCount
import BipartiteDD.HexagonEven.LevelsHyp
import BipartiteDD.HexagonEven.LevelsForest
import BipartiteDD.HexagonEven.Delorme

/-! Axioms used by the even-q Hexagon group. Run `lake env lean BipartiteDD/HexagonEven/Axioms.lean`. -/

#print axioms BipartiteDD.HexagonEven.B6Form_nondegenerate
#print axioms BipartiteDD.HexagonEven.finrank_plane_char2
#print axioms BipartiteDD.HexagonEven.finrank_plane_all
#print axioms BipartiteDD.HexagonEven.card_lines_through_even
#print axioms BipartiteDD.HexagonEven.exists_walk_even
#print axioms BipartiteDD.HexagonEven.genPolygonGraph_hexagon_even
#print axioms BipartiteDD.HexagonEven.hexagon_q2
#print axioms BipartiteDD.HexagonEven.card_spt_q2
#print axioms BipartiteDD.HexagonEven.plane_not_piE
#print axioms BipartiteDD.HexagonEven.finrank_planePiE
#print axioms BipartiteDD.HexagonEven.exists_slineE
#print axioms BipartiteDD.HexagonEven.slineE_unique
#print axioms BipartiteDD.HexagonEven.card_gE
#print axioms BipartiteDD.HexagonEven.card_zeros_PiE
#print axioms BipartiteDD.HexagonEven.card_pointsPiE
#print axioms BipartiteDD.HexagonEven.card_slineE
#print axioms BipartiteDD.HexagonEven.sline_edistE
#print axioms BipartiteDD.HexagonEven.exists_levelled_hexagon
#print axioms BipartiteDD.HexagonEven.delorme_bound_hexagon
#print axioms BipartiteDD.HexagonEven.delorme_bound_hexagon_two
#print axioms BipartiteDD.HexagonEven.whiskers_bound_hexagon
#print axioms BipartiteDD.HexagonEven.exists_aniso_even
#print axioms BipartiteDD.HexagonEven.card_hline_even
#print axioms BipartiteDD.HexagonEven.JE_JE
#print axioms BipartiteDD.HexagonEven.Qf_JE
#print axioms BipartiteDD.HexagonEven.Bf_JE
#print axioms BipartiteDD.HexagonEven.tits_JE
#print axioms BipartiteDD.HexagonEven.exists_hline_JE
#print axioms BipartiteDD.HexagonEven.key_cleared
#print axioms BipartiteDD.HexagonEven.exists_goodCubicE
#print axioms BipartiteDD.HexagonEven.plane_not_piZE
#print axioms BipartiteDD.HexagonEven.slineZE_unique
#print axioms BipartiteDD.HexagonEven.no_second_line'
#print axioms BipartiteDD.HexagonEven.slineZE_opp'
#print axioms BipartiteDD.HexagonEven.cond_iff
#print axioms BipartiteDD.HexagonEven.exists_unique_wline_even
#print axioms BipartiteDD.HexagonEven.ncard_wsetE
#print axioms BipartiteDD.HexagonEven.wset_whiskers_even
#print axioms BipartiteDD.HexagonEven.theoremD_even
#print axioms BipartiteDD.HexagonEven.theoremR
#print axioms BipartiteDD.HexagonEven.theoremR_two
#print axioms BipartiteDD.HexagonEven.theorem4_even
