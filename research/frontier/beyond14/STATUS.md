# beyond-d14: status at stop (2026-11-02 01:13 UTC, stopped by Doğa for budget)

Checked values (director checks; logs in research/frontier/runs/cloudcheck/ and research/frontier/beyond/graphs/):

| cell | before (beyond-d13) | now | check |
|---|---:|---:|---|
| (3,14) | 5,706 | 7,004 | apsp (2+2 base lifted over Z103 x\| Z17) |
| (4,14) | 497,042 | 504,382 | build_haar2 (Z6151 x\| Z41) |
| (5,14) | 12,795,166 | 13,467,134 | build_haar2 (Z100501 x\| Z67) |
| (6,14) | 187,990,656 | 193,539,888 | haarcheck_gen (SL(2,107) x Z79) |
| (7,14) | 1,674,490,944 | 1,732,018,320 | haarcheck_gen (SL(2,179) x Z151) |
| (9,14) | none | 20,002,113,120 | haarcheck_gen (PSL(2,241) x Z1429) - new cell |
| (10,14) | none | 20,002,113,120 | the (9,14) graph by monotonicity - new cell |
| (3,13) side | 3,400 | 4,324 | apsp (2+2 base over Z47 x\| Z23) |
| (3,12) side | 2,368 (lab) | 2,436 | apsp (2+2 base over Z87 x\| Z7) |

Also: the Foster census graph CSS(6272,7) (6,272, diameter 14) checked with apsp (not ours).

Unchecked (checks stopped at the end): (10,14) PSL(2,239) x Z1789, 24,422,855,520 vertices (sols/d10D14_psl_239_1789_orb3-3-1_s1.txt,
search cost 0); (7,14) PSL(2,1201), 1,732,322,400 (sols/d7D14_psl_1201_1_orb3-2-1_f14.txt, search cost 0).

Left open: (7,14) SL(2,359) x Z19 at cost 1 (879M, research/squads/beyond14/r5/g12/r_sl359_19.sol.low); (6,14) SL(2,71) x Z271 at
cost 3; (4,14) Z7211 x| Z35 at cost 1 (no single change closes it); (3,14) cost-2 2+2 lifts at 7,072-7,104 (strict local
minima); (3,11) cost 2 at 1,368 (lab 1,344); (8,14) not attempted. Round 6 was stopped after ~10 minutes.

Housekeeping: a round-5 card created an empty remote session session_01QYEEyHR8yEW2Yd8tMxxCbF (idle, no prompt, 0 tokens)
against the rules; it can be archived. Table rows: research/frontier/beyond/BEYOND_TABLE.md (section "D = 14 raises ...").
