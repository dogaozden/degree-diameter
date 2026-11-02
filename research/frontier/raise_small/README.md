# raise_small: job raise-small-d (2026-11-01/02)

Opus director + Haiku squads on the cells (Δ, D) with Δ = 3, 4 and D = 9..14. Results and discussion:
research/frontier/beyond/BEYOND_TABLE.md (rows and the section "Δ = 3, 4 at D = 9..14 (job raise-small-d)", whose
text is SECTION_RS.md); squad log research/squads/LOG.md; cards and scoreboards research/squads/raise-small/r1..r5.

## Values (all re-checked by the director)

| cell | value | graph | solution | check |
|---|---:|---|---|---|
| (3,12) | 2,436 | 2+2 cubic lift over Z29 x\|_7 Z21 | sols/d3D12_n2436_lift2_meta29_21_7.sol | checks/…apsp.txt |
| (3,13) | 4,324 | 2+2 cubic lift over Z47 x\|_2 Z23 | sols/d3D13_n4324_lift2_meta47_23_2_d02.sol | checks/…apsp.txt |
| (3,14) | 7,224 | 2+2 cubic lift over Z129 x\|_11 Z14 | sols/d3D14_n7224_lift2_meta129_14_11.sol | checks/…apsp.txt |
| (4,12) | 74,118 | Haar graph of Z1123 x\|_60 Z33 | ../sols/d4D12_meta_1123_33_60_e10.txt | checks/d4D12_…check.txt |
| (4,13) | 193,058 | Haar graph of Z1163 x\|_102 Z83 | ../sols/d4D13_meta_1163_83_102_dir.txt | checks/d4D13_…check.txt |
| (4,14) | 498,798 | Haar graph of Z3079 x\|_568 Z81 | ../sols/d4D14_meta_3079_81_568_c15.txt | checks/d4D14_…check.txt |

Earlier (smaller) valid lifts from this job are also in sols/ and checks/ (3,648, 3,696, 3,744 at D = 13; 6,528, 6,600
at D = 14; 7,008 and 7,040 at D = 14). Edge lists of all cubic lifts: research/frontier/beyond/graphs/d3D1*_lift*.edges.gz with their apsp logs.

## Rebuilding and checking

- Cubic lifts: `python3 tools/sol2edges.py SOL m k r OUT.edges` (vertex (u, g) = u N + g with g = a k + j; base edge
  "u v x" gives (u, g) ~ (v, g x); the product (a,j)(b,l) = (a + r^j b mod m, j + l mod k) is recomputed here), then
  `bin/apsp OUT.edges 3 D` (research/lifts/coordinator_check/apsp.c). tools/savelift.sh does both and stores the result.
- Haar graphs: `python3 tools/metacheck.py SOL` (independent numpy BFS from (e,A) and (e,B)); `python3
  tools/meta2edges.py SOL OUT.edges` + `bin/apsp OUT.edges 4 D` for the all-pairs check.
- Build: `gcc -O3 -march=native -fopenmp -o bin/X tools/X.c -lm` (bin/ is not committed); copied tools keep their
  origin in the file name (os_ = job own-small; hmeta, lift*, scan_h02, meta*check, enumeta = job beyond-d13;
  exh3, sweep_meta = job new-cells-beyond).

## Tools written here

- gtab.py (group tables in the salift_s format for (Z_m x|_r Z_k) x Z_c), glist.py (metacyclic groups by order),
  frob.py (Frobenius groups Z_p x| Z_k), mkbin.py (tables for exh3).
- scanlift.sh (salift_s over a group list, finds checked with apsp), chain.sh (continue a state; BIN=salift4 DEG=4 for
  quartic), pool.sh (chain all near misses of a scan), hscan.sh (fresh-seed hmeta over a group list), savelift.sh.
- tabu1.c (exhaustive 1-move tabu walk), saliftt.c (salift_s + targeted voltage moves), farpairs.py (lists the far
  pairs of a state). None of the last three beat plain annealing (BEYOND_TABLE section).
