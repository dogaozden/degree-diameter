# (16,6): 940,846 vertices (table 884,062, Delorme 1985)

Construction (Problem 4, research/p4/hats/REPORT.md v3, Theorem 4 with m = 3): generalized hexagon H(13), Delorme's
1985 3-ary levels around a Hermitian spread (884,062 vertices, the table value) with the exact set of 28,392 whiskers
added at level 0 (each whisker contributes m−1 = 2 copies). Rebuild:
`python3 research/p4/hats/hexbig.py 13 1800 build --load --arity=3` (whisker set research/p4/hats/whiskers_big_q13.json).

File: 940846-p4-hexagon-H13-3ary-exact-whiskers.edges.txt.gz — plain edge list, first line n, then "u v" per line.
sha256 of the uncompressed file: b04ffc08dbca518cfe3db074a0b28361d63ac18d5047ecc5d9a7c330a89b71a9

Checked 2026-10-20 by the main session's research-lab/verify/bigcheck (written without seeing the agents' code):
VALID — simple, max degree 16, bipartite (463862 / 476984), connected, exact diameter 6 (BFS from every vertex, 25 min
on 8 threads). The agents' C checkers were run as well (see the report).
