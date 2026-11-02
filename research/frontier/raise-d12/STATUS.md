# raise-d12: status at stop (2026-11-02 ~01:10 UTC, stopped on Doğa's budget instruction)

Found and checked (haarcheck_gen from (e,A) and (e,B); solutions in research/frontier/sols/, logs in
research/frontier/runs/cloudcheck/):
- (8,12) 297,777,408 (was 284,095,056), SL(2,128) x Z71, field-automorphism 7-orbit.
- (9,12) 1,178,527,488 (was 1,105,785,120), SL(2,128) x Z281.
- (10,12) 3,888,487,944 (was 3,712,424,352), PSL(2,243) x Z271, two 5-orbits.
- (11,12) 11,780,253,144 (was 11,189,148,096), PSL(2,243) x Z821 (Z811: 11,636,766,504, also VALID).
- (15,12) 29,999,670,624, new cell, PSL(2,197) x Z3924.
- Bonus outside the D = 12 brief: (17,10) 7,762,627,224, (20,8) 130,354,752, (17,8) 41,967,552.

Left / not done:
- (3..7,12): no raise; 33 squad cards in 3 rounds found only structural walls (research/squads/LOG.md).
- (12..14,12): at the 30-billion cap; exact-cap regraphs (< 0.02 %) not done.
- Near misses at one clump, not finished: (20,8) SL(2,32) x Z2011, (17,8) SL(2,32) x Z661.
- Leads not run: D = 14 cells, e.g. (7,14) SL(2,128) x Z421 (fieldfit.py, BEYOND_TABLE section).
- Coordinator: GF(2^e)/GF(3^5) graphs need haarcheck_gen for the reference re-check; (15,12) needs haarcheck_psl SOL A / SOL B.

Write-up: research/frontier/beyond/BEYOND_TABLE.md; tool: haar_bigq.c (README.md here); draft PR #535.
