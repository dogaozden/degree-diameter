# (13,6): 388,972 vertices (table 374,452, Delorme 1985)

Construction (Problem 4, research/p4/hats/REPORT.md): generalized hexagon H(11), Delorme's 1985 doubling with levels
around a Hermitian spread (374,452 vertices, the table value), plus an exact set of q²(q²−1) = 14,520 "whisker" line
copies. Generator: `python3 research/p4/hats/hexbig.py 11 1800 build` (whisker set research/p4/hats/whiskers_big_q11.json).

File: 388972-p4-hexagon-H11-whiskers.edges.txt.gz — plain edge list, first line n, then "u v" per line (2,511,132 edges).
sha256 of the uncompressed file: fa98ff43b03a391c6bb4b75d73f25c71817ca3b7a522661210d1551c0538afed

Checked 2026-10-20 by two independently written C checkers:
- research-lab/verify/bigcheck (main session; written without seeing the agents' code): VALID — simple graph,
  max degree 13 (12:34372, 13:354600), bipartite (193164 / 195808), connected, exact diameter 6 (BFS from every vertex).
- research/p4/d6/diam.c (the agents' bit-parallel checker): max degree 13, no pair farther than 6.
scripts/verify_record.py (Python) is too slow at this size.
