# fresh-6-5 work area

Tools (`tools/`):
- `bicoset.g` (GAP): `ExportBicoset(G, L, R, file, label)` writes the coset action tables of a bi-coset graph
  B(G; L, R; D); `ExportOrbitHaar(K, alpha, file, label)` writes the same data for the Haar graphs of K with
  alpha-invariant connection set. `CountUnions` counts candidates.
- `bicoset.c`: exhaustive scan of every union of L-orbits with valency 6; BFS from both base vertices (G is transitive
  on each side); cost = vertices beyond distance 5. Writes the first cost-0 graph as an edge list for apsp.c.
  Validated on the A3(2) chamber graph (630, apsp VALID).
- `scan_orbit.g` + `scan_dir.sh`: all groups K of order n in a window, all automorphism classes of order 2, 3, 5, 6.
- `weyl_graphs.py`, `weyl_scan6.py`: the building scan from the (16,5) run at maximum degree 6.
- copies of `haar_sym.c`, `lift.c` (+ python helpers) and `apsp.c` from their branches, for the squad cards.
