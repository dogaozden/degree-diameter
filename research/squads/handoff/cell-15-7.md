# Handoff: job cell-15-7 (resume session 01P3FWCNGZp2xTc6sYGPNtj4, branch claude/cell-15-7-haar-search-x6ynhl, PR #352)

State (details: research/squads/cells/d15D7.md, research/d15D7b/README.md, research/d15D7b/RELAXED.md):
- (15,7) best **2,501,491** (level types HHDHDHD, research/frontier/sols/d15D7_hex11_typedrelax2_n2501491.sol; BFS-checked),
  and **2,501,124** (table 2,480,184; master 2,497,075 at the start; cell-14-7's candidate 2,499,748):
  research/frontier/sols/d15D7_hex11_typedrelax_n2501124.sol, check research/d15D7b/checks/d15D7_hex11_typedrelax_n2501124.check.txt
  (theorem + BFS from all hubs and paired-element vertices; plain apsp_mt all-pairs run: RESULT VALID d=15 D=7). Earlier steps 2,500,147 / 2,500,749 / 2,501,008 are filed too (same check format).
- The earlier session's 2,480,280 (7 copies + freed flags) is merged in and superseded.

What limits it: n = 14·177,156 + min(|P0|, |P1|) + min(|S3|, |S4|) + 4·768, where P0, P1 (points freed at 0->2, 1->2) and
S3, S4 (lines freed at 2->3, 2->4) may contain pairs (RELAXED.md). Plain non-collinear / non-concurrent sets seem capped
at 8,645 / 8,246 (squad round c157b-r1, 8 cards, all negative); mirrored sets at 768 (pairwise-opposite mirrored sets are
partial ovoids of H(11); the 756 base is rigid). Relaxed sets: 9,306 points without coverage limits, ~9,117 with them.

If resumed, the most promising directions:
1. With the HHDHDHD pattern the bottleneck sets are free 1-defective sets (no coupling), so any better ILS for large
   1-defective point / line sets of H(11) counts directly (+1 per element on the smaller of each pair). 10-minute dpack
   runs give ~9,280 points and ~8,940 lines; the plain (non-collinear) optimum stays at 8,645.
2. The relaxation is generic: it applies to any friendly transition of a typed construction. (14,7) (5 levels HDHDH,
   cell-14-7's 1,789,588 = 10·177,156 + 2·(|R_L| + 768)) and (16,7) (q = 13, cell-16-7's 4,052,108) should gain several
   hundred vertices each with the same tools (tm3_build.py is written for HHDHHDD; the slot/demand logic is generic).
3. m > 768 would be worth 4 per element here: a partial ovoid of H(11) beyond 756 (none found by symmetric searches).
Scratch files are not kept: rebuild H(11) with research/d13D7/hexgen2.c 11 and the graphs from the .sol files.
