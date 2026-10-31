# selfdual-d6 records

No D = 6 record from this job. The two files below are **calibration graphs** (below the targets), kept to show the
search and check pipeline works at D = 6; each was rebuilt from its formula by an independent builder and checked by
research/lifts/coordinator_check/apsp.c (VALID at D = 6, INVALID at D = 5).

| file | cell | vertices | group, S | rebuild | sha256 of the (unzipped) edge list |
|---|---|---:|---|---|---|
| `d7D6_n4704_calib_sl7xz7.edges.gz` | (7,6) | 4,704 | SL(2,7) x Z7, self-dual S = [1 3 5 2]\|0 [5 3 5 6]\|0 [0 5 4 3]\|4 [4 5 4 0]\|3 [0 4 5 4]\|5 [3 4 5 0]\|2 [0 6 1 0]\|0 (psi(x) = -x^-1, z -> -z) | `build_d7D6_n4704_calib.sh` (build_sdhi.py) | 9893259bc72610b1f76f4defda9495f81a2a84e77bbce9b41e71a9df77c35404 |
| `d11D6_n29760_calib_psl31.edges.gz` | (11,6) | 29,760 | PSL(2,31), plain S in `d11D6_n29760_calib_psl31.sol` | `build_d11D6_n29760_calib.sh` (build_haar2.py) | 62a5f1592a07f4db57a66bbf85642863abae012e57c9fa0f5eea9a733651b143 |

Conventions: H(G,S) has vertices (g,A) and (g,B) and edges (g,A) ~ (s g, B). In the sdhi format [a b c d] is the
matrix with rows (a b), (c d) over GF(7) and "|z" is the Z7 coordinate. Vertex numbering and the .sol format are
described in the headers of `../src/build_sdhi.py` and `../../frontier/build_haar2.py`. Check output:
`*_calib_check.txt`.
