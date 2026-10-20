# (11,6): 146,545 vertices (table 142,464, Delorme 1985)

Construction (Problem 4, research/p4/d6/REPORT.md, p4-d6-opus): generalized hexagon H(9), Delorme's 1985 doubling with
levels around a Hermitian spread (142,464 vertices, the table value), plus 4,081 whisker line copies (not yet the exact
maximum 6,480, which would give 148,944). Rebuild: in research/p4/d6, `./hexgen 9; ./d6lift 9 2 0 1 out.txt graphs/h9_whisk*_W.txt`.

File: 146545-p4-hexagon-H9-whiskers.edges.txt.gz — plain edge list, first line n, then "u v" per line (789,659 edges).
sha256 of the uncompressed file: 54c622c481a23dadb965a841601ab76ee2cacdc4a4218db2273f41d35a29b70a

Checked 2026-10-20 by two independently written C checkers:
- research-lab/verify/bigcheck (main session): VALID — simple, max degree 11 (10:32677, 11:113868), bipartite
  (73750 / 72795), connected, exact diameter 6 (BFS from every vertex, 23.5 s).
- research/p4/d6/diamp.c (the agent's BFS from every vertex): diameter ≤ 6.
