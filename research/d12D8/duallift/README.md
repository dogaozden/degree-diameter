# research/d12D8/duallift: duality-hop lifts of H(9) (job own-12-8, 2026-10-26)

L levels, each a copy of the H(9) incidence graph, plus two hop edges per point x: (x, j) ~ (δx, j + t₁(x)) and
(δx, j + t₂(x)), δ a duality of H(9). 12-regular, bipartite, L·132,860 vertices (L = 35 would be the table value).
Result: random voltages reach L ≈ 10–12 only (table in research/squads/cells/d12D8_table.md §5.3); every far pair is a
point–line pair at hexagon distance 5.

- `conv_dual.py`: takes the duality from research/d10D7/dual/dualfind.c (run on hexgen2's H(9)) into the labels of
  ../omega/hexq6 (same model; points matched by coordinates) and checks it preserves all incidences.
- `duallift.c`: `duallift HEX DELTA L VOLT check STEP T` (pairs at distance > 8 from sources (s,0), s = 0, STEP, …;
  the level shift is an automorphism), `... diag S` (far vertices from one source by hexagon distance and level),
  `... edges OUT` (edge list for apsp). VOLT = file of "t1 t2" per point or `rand:SEED`.

```
gcc -O2 -o hexgen2 ../../d10D7/hexgen2.c && ./hexgen2 9          # writes hex/hex_q9.bin
gcc -O2 -o dualfind ../../d10D7/dual/dualfind.c && ./dualfind hex/hex_q9.bin d9
python3 conv_dual.py hex/hex_q9.bin d9.phi ../omega/hex_q9.txt delta_q9.npy
python3 -c "import numpy as np; np.savetxt('delta_q9.txt', np.load('delta_q9.npy'), fmt='%d')"
gcc -O3 -march=native -fopenmp -o duallift duallift.c
./duallift ../omega/hex_q9.txt delta_q9.txt 12 rand:1 check 2076 4
```
