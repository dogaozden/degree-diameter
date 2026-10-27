# Configuration family (heuristic)

`cfg_sa.c`: annealing over cubic bipartite graphs built from N 10-cycles and 5N/3 spoke pairs, each spoke pair joined
to antipodal pairs of 3 cycles and each cycle meeting 5 spoke pairs (n = 40N/3). This is the D = 7 analogue of the
extremal (3,5) graph on 56 vertices (7 six-cycles + 14 spokes on the Fano plane), suggested by the n = 248 structure
theorem (cell notes §2.6 item 7). Result (60 s runs, T 20 -> 0.3): N = 12 (n = 160): best cost 136 for three seeds;
N = 15 (n = 200): 1,128; N = 18 (n = 240): 4,252 (cost = ordered same-side pairs at distance > 6). The family does not
reach diameter 7 even below 168. The `.edges` files are the best states (diameter 8 or more).
