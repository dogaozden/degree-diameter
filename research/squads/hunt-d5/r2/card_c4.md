# Card c4 (round 2)

Read ../r1/PREAMBLE.md and ../r2/PREAMBLE.md first. Your folder: research/squads/hunt-d5/r2/c4/ (create it).

(9,5) route-chart controller at m = 17: a cubic bipartite graph with 17 + 17 vertices, every two same-side
vertices within distance 4, and every vertex on a 4-cycle. If found, `python3 rcq.py 3 CTRL ../charts/chart_q3_u0.txt
X.edges` + `apsp X.edges 9 5` gives a (9,5) graph on 2·3⁴·17 vertices, above our record 2,662. Three annealers stall at cost 6
(tools/ctrl, tools/ctrlpat with DIAG4=1). Use a different method: e.g. start from m = 16 solutions (`ctrl 16 … gen`)
and insert one A and one B vertex by rewiring 3 edges; tabu search; or an exact search (SAT / backtracking) over
graphs whose 4-cycles form a fixed pattern. Report the lowest cost at m = 17 and, if any, a proof idea for why 17 fails.
