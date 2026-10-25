# Rebuilding and checking the mirrored-surgery graphs (job cell-14-7, third session)

All graphs are (2r+1)-copy hexagon graphs built by research/d13D7/multi.c from a solution file in the multi_sol.py
format (header, freed points R', hub edges, the full bijection sigma). The rebuild is deterministic and gives the
byte-identical edge list (checked for every file below; sha256 in each check file).

```
cc -O2 -o hexgen research/d13D7/hexgen.c -lm            # q = 5, 7, 11, 13  -> hex/hex_q{q}.bin  (./hexgen q)
cc -O2 -o hexgen2 research/d13D7/hexgen2.c -lm          # q = 8 (GF(8))     -> hex/hex_q8.bin    (./hexgen2 8)
cc -O2 -fopenmp -o research/d13D7/multi research/d13D7/multi.c
python3 research/d13D7/tools/multi_sol.py build SOL hex/hex_q{q}.bin OUT.edges
```

| cell | n | solution (research/frontier/sols/) | q | check used here |
|---|---|---|---|---|
| (14,7) | 1,774,632 | d14D7_hex11_mirror768_n1774632.sol | 11 | `apsp_orb OUT 14 7 T 5 354312` VALID |
| (14,7) | 1,774,628 | d14D7_hex11_mirror767_n1774628.sol | 11 | `apsp_orb OUT 14 7 T 5 354312` VALID (superseded) |
| (14,7) | 1,774,588 | d14D7_hex11_mirror757_n1774588.sol | 11 | `apsp_orb OUT 14 7 T 5 354312` VALID (superseded) |
| (7,7) | 23,598 | d7D7_hex5_mirror81_n23598.sol | 5 | `apsp_mt OUT 7 7` VALID |
| (9,7) | 118,238 | d9D7_hex7_mirror295_n118238.sol | 7 | `apsp_mt OUT 9 7` VALID |
| (10,7) | 225,152 | d10D7_hex8_mirror229_n225152.sol | 8 | `apsp_mt OUT 10 7` VALID |
| (13,7) | 1,064,472 | d13D7_hex11_mirror768_n1064472.sol | 11 | `apsp_orb OUT 13 7 T 3 354312`: see checks/ |
| (15,7) | 2,484,792 | d15D7_hex11_mirror768_n2484792.sol | 11 | `apsp_orb OUT 15 7 T 7 354312`: see checks/ |
| (16,7) | 4,025,592 | d16D7_hex13_mirror813_n4025592.sol | 13 | `apsp_orb OUT 16 7 T 5 804468`: see checks/ |

apsp_orb and apsp_mt are research/lifts/coordinator_check/apsp_orb.c and apsp_mt.c. For apsp_orb the level shift
(x, i) -> (x, i+1) with hubs fixed is verified edge by edge before the BFS (level size B = 2|H(q)|).

The (13,7), (14,7) 1,774,632 and (15,7) graphs share one sigma and one R' (768 points); only r differs.
