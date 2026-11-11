# h6 notes (deep-65 round 2): wider hubtabu sweeps of the hub family

Start 03:22 UTC, end about 04:03 UTC. Single-threaded; every command under 110 s. No cost-0 state was found, so
no edge list was produced and no score65/apsp run was needed.

## Files
- hubtabu.c, hubk.c, score65.c, apsp.c: copies of round1/h4 (hubtabu = hubk with tabu mode). Built here.
- groups/: GAP tables for orders 236, 238, 240, 261, 264, 267, 270, 284 (all groups), 288 (88 sampled IDs).
  Generation: `gap -q -c 'ORDER:=O; IDS:=[...]; OUTDIR:="groups";' ../../tools/gap_tables.g`.
  Group counts (NrSmallGroups): 236:4, 238:4, 240:208, 261:2, 264:39, 267:1, 270:30, 284:4, 288:1045.
- screen.sh: `./screen.sh ORDER K SECS SEED ID...` runs hubtabu tabu once per group, appends to runs/screen.log.
- runs/: screen.log (all screens), deep_*.log (deep runs), ids288*.txt (288 sample IDs).

## Commands
- Screens: `./screen.sh O k 5 1 <all ids>` for orders 236, 238, 284, 261, 267 (5 s); k=2 order 240 and k=3 orders
  264, 270 at 3 s on all groups; k=4 order 288 at 3 s on 88 sampled IDs (offsets 1, 18 and 9 mod 35, see runs/ids288*.txt).
- Deep: `./hubtabu groups/sg_O_i.txt k tabu SECS SEED runs/edges_O_i_sSEED.txt 300 [TENURE]`.

## Results (best cost per (k, m); cost 0 = diameter 5; n = 2m + 2m/k)
| k | m | n | groups | best group (cost) | deep runs | notes |
|---|---|---|---|---|---|---|
| 2 | 236 | 708 | 4 | C118 x C2 (134, 5 s) | none | weak; C59:C4 cost 300 |
| 2 | 238 | 714 | 4 | C17 x D14 (6, seed 2, 40 s) | seed 3: 11 | |
| 2 | 240 | 720 | 208 | C3 x ((C5:C8):C2) = 240_112 (4) | seeds 2,3,4 (48-80 s): 4 each | miss pattern 4,0,0,0,0,0 |
| 2 | 240 | 720 | | C3:((C5:C8):C2) = 240_100 (7); C5 x GL(2,3) = 240_103 (8) | seed 2, 40 s | |
| 3 | 261 | 696 | 2 | C87 x C3 (198, 5 s) | none | abelian only |
| 3 | 264 | 704 | 39 | C11 x SL(2,3) = 264_12 (4) | seeds 2,3 (40 s): 4 each | 264_31 C11 x S4: 4 (seed 2) |
| 3 | 267 | 712 | 1 | C267 (222, 5 s) | none | |
| 3 | 270 | 720 | 30 | C5 x ((C3xC3):C6) = 270_10 (6) | seed 2, 40 s | 270_21 (C10 x ((C3xC3):C3)): 6 |
| 4 | 284 | 710 | 4 | C284 (300, 5 s) | none | all four 300-316: one orbit missing |
| 4 | 288 | 720 | 1045 (88 sampled) | (C3xC3):(C4:Q8) = 288_893 (13) | seeds 2,3 (40 s): 13 each | 288_351 ((C2^3):(C2^2)):C9: 15 |

Cost-floor observations: for 240_112, 264_12, 264_31, 288_893 the seeds return the same floor (4 or 13), with
miss vectors like 2,0,0,2,0,0 or 4,0,0,0,0,0 (orbit-sized misses), so this looks like a family limit for those
groups rather than a search failure. 238_1: 11 (5 s screen), 6 (seed 2, 40 s), 11 (seed 3, 40 s): not converged.

## Coverage caveats
- Screens are one seed of 3-5 s. A 4-cost screen ranking can be wrong (e.g. 238_1 was 11 at 5 s and 6 at 40 s).
- k=4 at 288 is an 88-group sample of 1045 groups (about 8%). It is not exhaustive.
- Abelian groups (236, 261, 267, and C2 x C118 etc.) are bad in every case tried.
- Machine load varied (GAP runs got 14 s CPU out of 105 s wall once). Screens were run with `nice -n 10`.

## Next steps (for whoever continues)
- Screen the remaining ~957 groups of order 288 at k=4 (about 3 s each, roughly 50 commands).
- Second and third seeds for 238_1 (k=2, n=714) and for 270_10 and 264_12 with longer stalls.
- An exact (hubk ex) check on the 264 C11-factor family (264_12, 264_31): the floor 4 may be structural.
