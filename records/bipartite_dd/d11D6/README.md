# (11,6): 148,944 vertices (table 142,464, Delorme 1985)

Construction (Problem 4, research/p4/hats/REPORT.md, p4-hats-opus): generalized hexagon H(9) over GF(9) (the built
incidence graph checks as the Moore graph: 132,860 vertices, 10-regular, diameter 6), Delorme's 1985 doubling with
levels around a Hermitian spread (142,464 vertices, the table value), plus an exact set of q²(q²−1) = 6,480 whisker
line copies (every free point covered once). Rebuild: `python3 research/p4/hats/hexbig_gf.py 9 1800 build --checkbase`.
Supersedes 146,545 (p4-d6-opus, non-exact whiskers, filed an hour earlier).

File: 148944-p4-hexagon-H9-exact-whiskers.edges.txt.gz — plain edge list, first line n, then "u v" per line.
sha256 of the uncompressed file: a84e59cbdba408153a3080a65b584588f3fa30783fc989ad00d97699a3f201cb

Checked 2026-10-20 by independently written C checkers:
- research-lab/verify/bigcheck (main session): VALID — simple, max degree 11 (10:15884, 11:133060), bipartite
  (73750 / 75194), connected, exact diameter 6 (BFS from every vertex, 17.5 s).
- research/p4/d6/diam.c and research/p4/hats/tools/check_big.c (agents): diameter ≤ 6, max degree 11.
