# raise-d9: status at stop (2026-11-02 01:10 UTC, stopped for budget)

Found (all haarcheck_gen VALID from (e,A) and (e,B); solution files in research/frontier/sols/, logs in checks/):
- (17,9) 553,208,880 (was 501,707,400, +10.3 %): SL(2,139) x Z103, ORBIT "3 5 2", mu 17.73 (FIXF finish).
- (18,9) 879,874,800 (was 790,626,816, +11.3 %): SL(2,149) x Z133, ORBIT "3 5 3", mu 21.22 (fresh FIXF run).
- (19,9) 1,328,920,800 (was 1,218,394,320, +9.1 %): SL(2,151) x Z193, ORBIT "3 6 1", mu 15.71.
- (20,9) 1,998,558,432 (was 1,823,175,864, +9.6 %): SL(2,233) x Z79, ORBIT "3 6 2", mu 16.16.
- Lower rungs also VALID and saved (8 more files). For the coordinator: these are below 20 billion vertices, so
  research/frontier/haarcheck_sl.c (or haarcheck_gen.c) checks them directly.
- New tool: haar_big1.c (haar_big0 + FIXF at D = 9: screen candidate orbits on the alpha-fixed elements; validated on 5 states).
- Findings: the plateaus at (17..20, 9) are inverse pairs of alpha-fixed torus elements; small p (97-240) with large n having
  one alpha-fixed z works, very small p (53-71) does not; central holes are rarer than the ODD_D_HOLES model.

Not raised: every D = 9 cell at Δ = 3..16 (4 squad rounds, 65 cards; best near misses (6,9) Frobenius Z1559 x| Z41 cost 2,
(15,9) PSL(2,151) x Z61 k = 5 cost 4, (8,9)/(11,9)/(12,9)/(14,9) cost 9-12). (3,9): exhaustive cubic Haar negative. Covers of
solved D = 9 Haar graphs cannot have diameter 9 (r3/w09).

Left when stopped (unfinished runs, states in runs/*.best): (17,9) SL(2,113) x Z193 mu 19.9 cost 6; (18,9) SL(2,107) x Z361
mu 23.3 cost 24; (19,9) SL(2,239) x Z49 mu 17.8 and (20,9) SL(2,107) x Z823 mu 19.1 just started; (6,9) farm at 62 seeds.
Write-up: research/frontier/beyond/BEYOND_TABLE.md (rows and section "D = 9 at Δ = 17..20, raised"), research/squads/LOG.md.
