# General-graph records (20 November 2026)

Cayley graphs of Z_m ⋊ Z_n, with product [x, y][u, v] = [x + u, y·r^u + v] (x, u in Z_n; y, v in Z_m; r of order n modulo m).
A witness file gives d, D, N = m·n, m, n, r and the generating set S (each listed element and its inverse is a generator).

| Folder | (Δ, D) | Vertices | Previous (Comellas's table, 20 Nov 2026) |
|---|---|---:|---:|
| `d8D7/` | (8, 7) | 139,965 | 139,867 |
| `d10D7/` | (10, 7) | 625,733 | 625,464 |
| `d10D8/` | (10, 8) | 4,538,823 | 4,524,979 |
| `d12D8/` | (12, 8) | 19,240,407 | 19,218,539 |

`check/independent_bfs.py WITNESS` (pure Python) and `check/verify_mc.py m n r D u1 v1 u2 v2 ...` (numpy) each rebuild the graph from the
group law, check the degree, and run a BFS from the identity (the graph is vertex-transitive, so this is the diameter). The `*.out`
files are their outputs for each record; `*.sha256` is the hash of the witness file.
