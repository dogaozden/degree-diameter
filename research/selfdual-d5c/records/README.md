# selfdual-d5c records

No record from this job. The two files here are the largest calibration graphs (below our values at (12,5) 9,840 and
(13,5) 11,700), kept as data points for the frontier of the self-dual Haar family.

- **(12,5) 6,984 vertices (calibration)**: Haar graph of G = C97 : C36 = <x, y | x^97 = y^36 = 1, y x y^-1 = x^6>,
  x^i y^j written (i,j), (i,j)(a,b) = (i + 6^j a, j + b), (g,A) ~ (s g, B),
  S = {(0,0), (0,15), (53,10), (86,5), (14,2), (68,13), (53,32), (89,19), (26,15), (58,0), (31,16), (65,35)}.
  Vertex (i,j) on side A is 36 i + j, on side B 3,492 + 36 i + j. Found by fsd (EXT record 91, f = 0). apsp VALID at
  D = 5, INVALID at D = 4 (`calib_d12D5_n6984_c97c36_apsp.txt`); independent rebuild identical to fsd's own edge list.
  `calib_d12D5_n6984_c97c36.edges`, sha256 5c7ade778c3a910ed64f18ac4f45c3aafb8ffecd3f038890633a2d5a53efa1bb.
- **(13,5) 10,040 vertices (calibration)**: Haar graph of G = C251 : C20, y x y^-1 = x^32, same conventions (vertex
  (i,j) on side A is 20 i + j), S = {(0,0), (79,10), (4,10), (5,19), (160,11), (68,12), (154,8), (44,13), (124,17),
  (34,1), (205,9), (29,7), (237,3)}. Found by fsd (ALPHA record 5, type (3,5)). apsp VALID at D = 5, INVALID at D = 4
  (`calib_d13D5_n10040_c251c20_apsp.txt`); independent rebuild identical to fsd's own edge list.
  `calib_d13D5_n10040_c251c20.edges`, sha256 a108e6c32db237e6e9d8ee130e4bc27f8aa2163b365c1ba9cdd98391879f8b1c.

Rebuild both: `bash build_calib.sh` (uses ../src/build_fsd_haar.py, prints the sha256 above).
