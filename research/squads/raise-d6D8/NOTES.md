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
