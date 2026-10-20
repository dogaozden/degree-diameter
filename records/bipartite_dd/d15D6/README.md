# (15,6): 870,440 vertices (table 842,048, Delorme 1985)

Construction (Problem 4, research/p4/hats/REPORT.md, p4-hats-opus): generalized hexagon H(13), Delorme's 1985 doubling
with levels around a Hermitian spread (842,048 vertices, the table value), plus an exact set of q²(q²−1) = 28,392
whisker line copies (ILP on 168 orbit variables under the symmetric ansatz). Rebuild:
`python3 research/p4/hats/hexbig.py 13 1800 build` (whisker set research/p4/hats/whiskers_big_q13.json).

File: 870440-p4-hexagon-H13-exact-whiskers.edges.txt.gz — plain edge list, first line n, then "u v" per line.
sha256 of the uncompressed file: 61b10395e67e5e55ec3ba14dacf6df7be23884a0edd7310236ee228592b58f58

Checked 2026-10-20 by independently written C checkers:
- research-lab/verify/bigcheck (main session): VALID — simple, max degree 15 (14:65580, 15:804860), bipartite
  (433034 / 437406), connected, exact diameter 6 (BFS from every vertex, 21 min on 8 threads).
- research/p4/d6/diam.c and research/p4/hats/tools/check_big.c (agents).
