# Card c3 (round 1)

Read ../r1/PREAMBLE.md first. Your folder: research/squads/hunt-d5/r1/c3/ (create it).

(9,5) controller search for a route-chart lift (director's lead; the director writes the chart and the lift).
Find cubic (3-regular) bipartite graphs C with m vertices on each side, m as large as possible (m = 18..26), such that
(i) every two vertices on the same side are at distance ≤ 4, and (ii) every vertex lies on a 4-cycle. Methods: Haar
graphs H(G, {e,a,b}) over all groups of order m (vertex-transitive: check one vertex per side), 2+2 / 3+3 base lifts
over groups of order m/2, m/3, and edge-switch local search on general cubic bipartite graphs. For each m report the
graph with the most 4-cycles per vertex. Score = 2m (largest m with (i) and (ii)); save edge lists as
c3/ctrl_m<m>.edges ("2m" then "u v" lines, side A = 0..m−1). A Python BFS is enough here (graphs are tiny).
