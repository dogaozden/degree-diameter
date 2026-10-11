# Candidate new records (bipartite degree-diameter)

Status: **verified graphs, literature check pending.** Not yet claimed as records.

Reference table: Combinatorics Wiki, "The Degree Diameter Problem for Bipartite Graphs"
(http://combinatoricswiki.org/wiki/The_Degree_Diameter_Problem_for_Bipartite_Graphs), last edited 2022.

| (Δ, D) | table record | ours | graph | found by | file |
|---|---|---|---|---|---|
| (4, 5) | 160 | **162** | 4-regular, 81 + 81 | C island c-d4d5, g002-c08 | d4D5/162-c-d4d5-g002-c08.json |
| (7, 4) | 346 | **354** | degrees 6–7, 172 + 182, 1204 edges | C island c-d7d4, g002-c13 | d7D4/354-c-d7d4-g002-c13.json |
| (7, 4) | 346 | 349 | degrees 6–7, 172 + 177, 1204 edges | Python island spec-d7d4, g003-c13 | d7D4/349-spec-d7d4-g003-c13.json |
| (11, 3) | 190 | **192** | 11-regular, 96 + 96 | C island c-d3fam, g001-c00 | d11D3/192-c-d3fam-g001-c00.json |

Verification (2026-10-10, on the Mac):
1. All four pass `scripts/verify_record.py`: the trusted checker, the networkx checker, and a
   from-scratch check (adjacency sets, explicit 2-colouring, BFS from every vertex for the exact diameter).
2. Each generating program (saved next to its graph as `*.program.py`) was re-run fresh on a different
   machine than the cloud island that found it, with seed 0 and a 60 s limit, and rebuilt the same order:
   162, 354, 349, 192.

Re-run the check: `python scripts/verify_record.py records/bipartite_dd/d4D5/162-c-d4d5-g002-c08.json 4 5`
