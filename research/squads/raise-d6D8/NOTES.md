# raise-d6D8 notes (Haiku worker, job "raise-6-8")

Goal: beat our (6,8) record of 31,680 vertices (psl 11 x Z24, ORBIT="2 3 0", N = |G| = 15,840).
Table value 29,790; Moore bound 195,312. Any Haar graph with 2|G| > 31,680 is a new record.

## Setup (2026-10-25)
- Tools: research/structured/ (haar_sym.c from claude/structured-search-orbit-04hefm, latest version incl. FIXMIN and RANDORB).
  Built: research/structured/haar_sym, research/structured/tools/haarcheck_psl.
- Winning run recipe (from claude/degree-diameter-table-squad-0xgp3g, runs/d6D8_psl_11_24_orb2f0_s1.log):
  `ORBIT="2 3 0" THREADS=1 ./haar_sym 6 8 <secs> <seed> 8 out.txt psl 11 24`; solved in 334k evals, 23.6 s, Fix(alpha)=23, mu=33.29.
- Table-squad negatives for k=2 above 15,840 (short runs, see their LOG.md): A4xPSL(2,7)xZ8 (16,128) stops at 5 in 4 seeds;
  SL(2,8)xZ32 (16,128) 7-12; PSL(2,19)xZ5 (17,100) 12; PSL(2,11)xZ25 (16,500) 14; PSL(2,13)xZ15 (16,380) 12; SL(2,16)xZ4 (16,320) 15;
  PSL(2,7)xZ95 and SL(2,5)xZ133 (15,960) >= 98 (screen).
- Effort law (structured-search §9.1): evals ~ 1e5 * exp((mu_A - 13)/2), mu_A ~ mu/k + fixed-point term. At k=2 and N~16k,
  mu ~ 34-36 and mu_A ~ 17-18, so the law predicts ~1e6 evals (about 1-2 min at ~14k evals/s). Long runs are cheap.

## Screen
- research/squads/raise-d6D8/screen_2_3_0_15841_16700.txt: orb_screen.py 6 8 15841 16700 "2 3 0" --anyn --samples 20000.

## Log
(append below: time, what ran, result)

- 08:07-08:22 wave 1 (ORBIT="2 3 0", 900 s, seed 1, THREADS=1), all NO solution:
  pgl 8 32 (N 16128, fix 15) best 8 after 9.5e7 evals; sl 7 48 (16128, fix 15) best 8; psl 13 15 (16380, fix 11) best 10;
  psl 11 25 (16500, fix 11) best 14. Plateaus form within ~60-120 s and do not move (same pattern as table-squad).
  Reference: psl 11 24 (15840, fix 23) solved in 3.3e5 evals (24 s), random-sample min 5 (20k samples) vs 8-12 at 16k.

## Alpha sweep (08:25-08:31): alpha_sweep.sh, ALPHA=index over all Q elements, RANDORB=5000, k=2 m=3 f=0
(tsv in alpha_sweep/, min = best random sample cost in elements; the winner's default alpha has min 5)
- psl 11 x Z24 CONTROL (N 15840): best min 4 (index 291), default alpha 557 min 5; 56 valid alphas, min 4..11.
- pgl 8 x Z32 (16128): best min 14 (106); sl 7 x Z48 (16128): best 17; psl 13 x Z15 (16380): best 10 (index 0);
  psl 11 x Z25 (16500): best 20. None close to the control: the 16k candidates are not winner-like for any alpha.

## Wider screen 15841-22000 (5000 samples, auto alpha): screen_2_3_0_15841_22000.txt
- best by min/p1: psl 19 x Z5 (N 17100, mu 56.6): min 18, p1 50; psl 17 x Z7 (17136) min 43; sl 13 x Z8 (17472) min 28;
  psl 13 x Z16 (17472) min 28; prod psl 3 x psl 7 x Z8 (16128) min 20 (table-squad: floor 5 for this group).
- Effort-law caveat: wave 1 (15-min runs at N 16k, mu_A ~ 21) used ~8e7 evals each and plateaued at 8-14, far above the law's
  ~5e6 prediction. So the law is not reliable for these groups; treat predictions as optimistic.

## Wave 2 (started 08:35): 20-min runs, seed 1 and 2 on psl 19 x Z5 (N 17100), seed 1 on sl 13 x Z8 (17472), psl 13 x Z16 (17472).

## Wave 2 (08:35-08:59, 1200 s): psl 19xZ5 seed1 best 10, seed2 best 8; sl 13xZ8 best 9; psl 13xZ16 best 13. No solution.
## Wave 3 (09:08-09:33, 600 s, one seed each): psl 17xZ7 14; psl 23xZ3 22; sl 11xZ13 20; psl 11xZ26 23; prod sl3xsl9 9;
   psl 9xZ48 19; prod psl3xsl7xZ4 9; prod psl3xpsl7xZ9 26; sl 9xZ24 21; prod psl3xsl4xZ23 21. No solution.
## Wave 4 (queued, starts after WAVE3_DONE, 5400 s, ORBW=3): psl 19xZ5 seed 3; sl 13xZ8 seed 2; prod sl3xsl9xZ1 seed 2;
   prod psl3xsl7xZ4 seed 2. Diagnostic: does the plateau move with ORBW=3? Results go to runs/*_orbw3_*.log.
Draft of the cell write-up: research/squads/cells/raise-d6D8.md.

## Wave 4 (09:30-11:00, 5400 s, ORBW=3): psl 19xZ5 s3 best 10; sl 13xZ8 s2 best 8; prod sl3xsl9xZ1 s2 best 10;
   prod psl3xsl7xZ4 s2 best 9. No solution. ORBW=3 does not move the plateaus.

## FINAL (11:00): stopped. No record raised. Total compute about 10 core-hours. Verdict and evidence in
   research/squads/cells/raise-d6D8.md. Best plateau above 15,840: 8 (sl 13xZ8, psl 19xZ5). Winner group is special.
   Not tried (need new code): non-cyclic abelian factors, metacyclic/Heisenberg k=2, random S above 15,840.
