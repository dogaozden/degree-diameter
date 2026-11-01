# h2 notes (deep-65 round 1, card h2: type "1,6,6|1,6,6" screen)

Start 02:38 UTC, stop 03:48 UTC. Single-threaded, all commands under 110 s.

## Setup
- Copied shared/mcos.c, score65.c, apsp.c here; built ./mcos ./score65 ./apsp (gcc -O3 -march=native).
- Group tables: GAP with OUTDIR=.../round1/h2/groups (absolute path needed). Candidate groups (nonabelian, with
  elements of order 6, from list.g): 258: ids 1,2,4 (3 groups); 264: ids 1,2,3,5..27,29,30,33..38 (34 groups);
  270: ids 2,5..15,17,19,21..27 (21 groups). Total 58.

## Calibration
- TYPE="1|1" SECS=25 SEED=4 EDGES=cal684.edges on SmallGroup(342,12) (sg_342_12.txt): cost 0 after 9.8 s
  (334k evals); score65 cal684.edges: n=684 bad=0 diam=5. mcos calibration OK.

## Screen (SECS=4, SEED=1, MAXCOMB=6, TYPE="1,6,6|1,6,6" N="4,1,1,1,0,0,1,0,0")
- Driver: screen_step.sh (resumable, queue.txt = 58 groups), per-group lines in screen.log, raw COMB/RESULT lines
  in screen_full.log. Groups: list.g (GAP) gives the candidate list (nonabelian, order-6 elements).
- Caveat: MAXCOMB=6 enumerates combos lexicographically, so for groups with >6 valid combos (classes 6, 10, 14, 26)
  only the first 6 are tried (A-classes mostly 0). The card asked for MAXCOMB=6, so this is as specified.
- Best screen cost per order: 688: 258_1 (C43:C6) 27; 704: 264_33 (A4 x D22) 72 (next 264_35 241, 264_12 246);
  720: 270_6 48 (next 270_7 76, 270_10 81, 270_11 81, 270_14 92, 270_15 92).
- Other orders 258: 258_2 165, 258_4 474. Most 264/270 groups are 200-1700.

## Deep runs (SECS 47-90 per seed, one best combo per group fixed by CLS)
| group | CLS | seeds: mcos cost (score65 bad) |
|---|---|---|
| 258_1 (688) | 0,0,0,0 | s1 27 (2408), s2 37 (2408), s3 38 (2752), s4 20 (2150), s5 21 (1634), s6 20 (2150) |
| 264_33 (704) | 0,1,1,1 | s1 74 (4268), s2 60 (3520), s3 72 (5104), s4 74 (4268) |
| 270_6 (720) | 0,0,0,0 | s1 48 (2880), s2 48 (2880), s4 48 (2880) |
- Same-cost graphs can have different bad counts and vice versa (bad is not monotone in mcos cost; mcos cost counts
  unreached pairs per orbit representative only, so it is not the total bad count).
- Best bad counts: 688: 1634 (seed 5, cost 21); 704: 3520 (seed 2, cost 60); 720: 2880 (cost 48).
  No graph has bad = 0, so apsp was NOT run. (Every graph has maxdeg 6, bipartite, simple, n as stated.)
- Saved graphs: best_n688_bad1634.edges, best_n704_bad3520.edges, best_n720_bad2880.edges (copies of
  e258_1_s5.edges, e264_33_s2.edges, e270_6_s1.edges in this folder).

## Reading
- This type is far from diameter 5: best bad counts are in the thousands (vs 144 for the 684+2 insertion route).
  The 720 group saturates at cost 48 in every seed, which looks structural for this N split.
- Not done (time): other N splits for these groups, other class combos for 264_33 and 258_1 at depth, the
  remaining 264/270 groups at depth.

## Later additions
- 258_1 seed 7 (SECS=90, CLS=0,0,0,0): cost 21, bad 1634 (same bad count as seed 5; file e258_1_s7.edges).
- 270_6 seed 3 (SECS=47, CLS=0,0,0,0): cost 48, bad 2880 (file e270_6_s3.edges).
- Total deep seeds: 258_1 7, 264_33 4, 270_6 4 (incl. screen seed 1 at SECS=4).
- Final: 688 best cost 20 (bad 2150), best bad 1634; 704 best cost 60, best bad 3520; 720 cost 48, bad 2880.
