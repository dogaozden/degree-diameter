# General-graph records (20–21 November 2026)

Cayley graphs of Z_m ⋊ Z_n, with product [x, y][u, v] = [x + u, y·r^u + v] (x, u in Z_n; y, v in Z_m; r of order n modulo m).
A witness file gives d, D, N = m·n, m, n, r and the generating set S (each listed element and its inverse is a generator).

| Folder | (Δ, D) | Vertices | Previous (Comellas's table, day found) |
|---|---|---:|---:|
| `d8D7/` | (8, 7) | 139,965 | 139,867 |
| `d10D7/` | (10, 7) | 625,733 | 625,464 |
| `d10D8/` | (10, 8) | 4,538,823 | 4,524,979 |
| `d12D8/` | (12, 8) | 19,240,407 | 19,218,539 |
| `d10D9/` | (10, 9) | 34,934,046 | 34,913,494 |
| `d7D9/` | (7, 9) | 1,338,558 | 1,332,774 |
| `d7D10/` | (7, 10) | 6,692,790 | 6,645,690 |
| `d9D10/` | (9, 10) | 90,493,830 | 89,658,816 |
| `d8D10/` | (8, 10) | 27,036,394 | 27,019,307 |

`check/independent_bfs.py WITNESS` (pure Python) and `check/verify_mc.py m n r D u1 v1 u2 v2 ...` (numpy) each rebuild the graph from the
group law, check the degree, and run a BFS from the identity (the graph is vertex-transitive, so this is the diameter). The `*.out`
files are their outputs for each record; `*.sha256` is the hash of the witness file.

The first five folders (found 20 Nov, plus (10, 9)) are Z_m ⋊ Z_n witnesses as above. `d7D9/`, `d7D10/`, `d9D10/`, `d8D10/` are
Cayley graphs of F_p² ⋊ Q, Q = Z_k ⋊ Z₂ < GL(2, p) (product (u, v)(x, y) = (ux, ρ(x)⁻¹v + y)): the witness `.txt` gives the group and generators,
`*.bin` is the list of Q's matrices, `build_q.py` rebuilds it, and three checkers are included with their outputs: `cay_mg.c` (bitset BFS,
the search engine), `bfs_g.c` (explicit element-wise BFS in C) and `indep_g2.py` / `indep_np.py` (matrix arithmetic in Python / numpy).
Example: `bfs_g d7D9/group_F131sq_Z39_Z2.bin 7 78  7 9 56  13 10 112  57 29 63  2 0 68`. `d10D9/` has the C BFS `bfs_c.c` next to the Python one.
