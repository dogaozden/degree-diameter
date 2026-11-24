# General-graph records

Cayley graphs of Z_m ⋊ Z_n, with product [x, y][u, v] = [x + u, y·r^u + v] (x, u in Z_n; y, v in Z_m; r of order n modulo m).
A witness file gives d, D, N = m·n, m, n, r and the generating set S (each listed element and its inverse is a generator).

<!-- dd-publish:folders -->
| Folder | (Δ, D) | Vertices | Previous (Comellas's table, day found) |
|---|---|---:|---:|
| `d8D7/` | (8, 7) | 139,965 | 139,867 |
| `d14D8/` | (14, 8) | 65,707,429 | 65,587,703 |
| `d10D9/` | (10, 9) | 34,934,046 | 34,913,494 |
| `d7D9/` | (7, 9) | 1,338,558 | 1,332,774 |
| `d7D10/` | (7, 10) | 6,692,790 | 6,645,690 |
| `d9D10/` | (9, 10) | 90,493,830 | 89,658,816 |
| `d8D10/` | (8, 10) | 27,498,631 | 27,019,307 |
| `d10D8/` | (10, 8) | 4,575,965 | 4,524,979 |
| `d12D8/` | (12, 8) | 19,426,693 | 19,218,539 |
| `d10D10/` | (10, 10) | 269,448,857 | 265,782,337 |
| `d10D7/` | (10, 7) | 625,791 | 625,464 |
| `d11D10/` | (11, 10) | 702,594,702 | 697,429,356 |
| `d12D10/` | (12, 10) | 1,698,992,742 | 1,693,260,247 |
| `d13D9/` | (13, 9) | 366,922,490 | 362,847,996 |
| `d13D10/` | (13, 10) | 3,796,611,270 | 3,789,512,750 |
| `d15D8/` | (15, 8) | 110,624,094 | 110,182,818 |
<!-- /dd-publish:folders -->

`check/independent_bfs.py WITNESS` (pure Python) and `check/verify_mc.py m n r D u1 v1 u2 v2 ...` (numpy) each rebuild the graph from the
group law, check the degree, and run a BFS from the identity (the graph is vertex-transitive, so this is the diameter). The `*.out`
files are their outputs for each record; `*.sha256` is the hash of the witness file.

The first five folders (found 20 Nov, plus (10, 9)) are Z_m ⋊ Z_n witnesses as above. `d7D9/`, `d7D10/`, `d9D10/`, `d8D10/` are
Cayley graphs of F_p² ⋊ Q, Q = Z_k ⋊ Z₂ < GL(2, p) (product (u, v)(x, y) = (ux, ρ(x)⁻¹v + y)): the witness `.txt` gives the group and generators,
`*.bin` is the list of Q's matrices, `build_q.py` rebuilds it, and three checkers are included with their outputs: `cay_mg.c` (bitset BFS,
the search engine), `bfs_g.c` (explicit element-wise BFS in C) and `indep_g2.py` / `indep_np.py` (matrix arithmetic in Python / numpy).
Example: `bfs_g d7D9/group_F131sq_Z39_Z2.bin 7 78  7 9 56  13 10 112  57 29 63  2 0 68`. `d10D9/` has the C BFS `bfs_c.c` next to the Python one.

## How this directory is kept current

`records/RECORDS.csv`, the folders here, the tables between `<!-- dd-publish:… -->` markers in this file and in the top-level `README.md`
(the "Where things stand" numbers and the general-graph table) are generated from the lab's records directory by an automated publisher,
which refuses to push if a check fails (consistent counts, every check output verifying the stated order, degree and diameter, a
privacy/secrets scan of the diff). Edit those parts at the source, not here; text outside the markers is hand-written. A folder is
written once per cell and replaced only when a larger graph for the same (Δ, D) is filed.
