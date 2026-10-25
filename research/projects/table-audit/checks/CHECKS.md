# Checks (table-audit)

Checkers (coordinator's, unchanged): `research/lifts/coordinator_check/apsp.c` (all-pairs bit-parallel BFS, no symmetry:
simple, max degree, bipartite, connected, exact diameter), `apsp_mt.c` (same, threaded), `apsp_orb.c` (BFS from one
level of a level cover after checking edge by edge that the level shift is an automorphism). Build: `cc -O2 [-pthread]`.

| log | what | how it was made |
|---|---|---|
| moore_pg_w.txt | PG(2,q) and W(q) incidence graphs, q = 2..13 (18 Moore cells, D = 3, 4) | `sh tools/rebuild_small.sh WORKDIR` |
| moore_h_small.txt | H(q), q = 2, 3, 4, 5, 7, 8 (D = 6) | same |
| h_9/11/13.apsp.txt | H(9), H(11), H(13) | `moore_build h q g/h_q.txt` then `apsp_mt g/h_q.txt q+1 6 4` |
| small.txt | 31 small cells: (3,5) BYE and annealed; Hafner's 7.3, 4.5, 4.7, mdec3.7; (7,3) Haar; C168.1; FMP Φ95 ×3; AL q = 9, 11, 13; (16,3); Delorme D = 4 ×5; (7,6); Delorme §9 (6,7), (8,7); D = 5 covers ×6; (7,7) cover; Haar reproductions in graphs/*.sol | `sh tools/rebuild_small.sh WORKDIR` |
| d6_q9/11/13_b2.apsp.txt, d6_q13_b3.apsp.txt | Delorme §8(b) at q = 9, 11, 13 (doubling) and q = 13 (tripling): (11,6), (13,6), (15,6), (16,6) | `BIN=.. G=.. python3 tools/delorme.py d6 q b OUT` then `apsp_mt OUT q+b-1 6 4` |
| x7_dΔ.apsp.txt | D = 7 covers: 2j+1 copies of H(q) and j bijections, Δ = 7, 9..16 | `python3 tools/xt_build.py g/h_q.txt j OUT` then `apsp_orb OUT Δ 7 4 2j+1 2·|points|` |
| d13D5_n11664_BH_mizuno.txt | B(H) of Mizuno's (12,4) graph: (13,5) ≥ 11,664 | download (URL in the log), `python3 -I tools/closed_double.py IN OUT`, `apsp OUT 13 5` |

Base geometries come from `tools/moore_build.c` (`moore_build pg|w|h q EDGES [COORDS]`).
