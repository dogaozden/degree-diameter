# c3 notes (bi-coset graphs of almost simple groups, |H| = |K| >= 4)

Pipeline: `runone.sh LABEL "GAP_EXPR" H` runs shared/dc_export.g (all class pairs of core-free subgroups of order H,
double cosets written to out/LABEL_hH_i_j.dc) then shared/dcenum FILE 6 5 (exhaustive unions of double cosets with
degree 6; cost = missed BFS pairs from the two base points). Results appended to results.txt. gap/cands.g lists groups.

Calibration: PSL(4,2) = A8 with Borel (H=K=B, order 64): dcenum finds cost 0 at n=630 (check.sh: bad=0 diam=5). OK.

Done (exhaustive, all admissible h = 2|G|/n with n in 686..800 and h >= 4):
- A7 h7, S7 h14, A8 h56, PSL(4,2) h56, PSL(3,4) h56 (no class), S8 h105/112 (none), S9 h1008 (none), A9 h480/504
- PSL(3,3) h16 (n=702, best cost 64, bad 11232), PSU(3,3) h16 (756, best cost 384 bad 72576)
- PSp(4,3) h72 (720, cost 1404), M11 h20 (792, cost 350), M11 h22 (none), M12 h240/264/270 (none)
- PSL(2,q), PGL(2,q): q=13 (PGL h6: cost 44, n 728), 19 (PGL h18 none, h19 cost 1368), 25 (PSL h20 cost 128),
  27 (PSL h26/27/28, PGL h52/54/56; best 1404), 29, 31, 32, 49 (147: 1568), 64, 81 (none)
- PGammaL(2,8) h4 (n=756): cost 24 (bad 4536). Best of the run so far.

Card idea not yet done: PSL(2,q).k with field automorphisms, G2(3) (L3(3):2 n=756, U3(3):2 n=702), PSp(4,3).2 (h 135, 144),
PSU(3,3).2 (h 32), products PSL(2,q) x C_k, metacyclic Z_p:C_6 (p = 349, 367, 373, 379, 397 with Frobenius bi-coset),
affine V:H0 with V=F_7^3 (n=686) or F_19^2 (n=722) and small H0.

## update 16:15 UTC
- Field-automorphism extensions: PSigmaL(2,25) h39/40 (best cost 1536), PSigmaL/PGammaL(2,27) h78-168 (best 1404),
  PSigmaL(2,49) h294/300/336 (1568), PGammaL(2,32) h440/465 (none exported). Nothing new.
- PSL(2,25) h20 (n=780) cost 128 (bad 24960); PSL(2,27) h27 cost 1404 (n=728, bad 255528).
- Frobenius-type Z_p:C_6 for p = 349, 367, 373, 379, 397 (bi-coset with H = complement): cost ~1100-1300. Bad.
- Affine F_q : C_k with H = C_h, index j = k/h >= 2 (non-Haar: V is not regular on G/H), 55 cases (aff_candidates.txt).
  Best: q=121, k=12, h=4 (n=726) cost 120 (bad 21780); q=97, k=16, h=4 (n=776) cost 128 (bad 24832);
  q=61, k=30, h=5 (n=732) cost 340. Nothing reaches 0.
- Note: complement bi-coset graphs B(V:H0, H0, H0) with V regular normal of order 343..400 are Haar graphs
  H(V,S) with S a union of H0-orbits, so they are already covered by haarex3 (not repeated here).
- Scoreboard: best so far with n>684 is PGammaL(2,8) h=4, n=756, bad=4536 (far pairs from check).
- Running now: product groups T x C_k (T in A5,S5,PSL(2,7),PGL(2,7),A6,PSL(2,8),S6,PSL(2,11),PSL(2,13),...; k<=10).
- Tool notes: GAP NrSmallGroups() and the smallgrp package are too slow here (timeouts); avoid SmallGroups for big orders.

## ideas not yet done (for the next round)
- Biregular bi-coset graphs: |H| = h1 != |K| = h2 with h1 = 6*h2/d_B, d_B = 6*h2/h1 <= 6 (A-side degree 6, B-side
  degree d_B; the max-degree-6 goal allows it). Needs dc_export with two orders; examples (h1,h2) = (6,4), (6,5),
  (8,4), (12,6), (9,6), (10,5). Not in the card; not run.
- Capped unions (tested = 300000) were only partially searched; sa_capped.sh runs dcenum SA mode on them.
- SmallGroup-library sweeps of orders 343*h..400*h (h >= 4) were not done: GAP smallgrp is too slow here.

## final (stopped at the 17:45 UTC deadline; the clock read 21:08 when the sweep finished)
- Product sweep T x C_k (k <= 10; T = A5, S5, PSL(2,7), PGL(2,7), A6, PSL(2,8), S6, PSL(2,11), PSL(2,13), PSL(2,17), S4, PSL(2,19), A4): 24 groups exported, no solution.
  Best bad: A6 x C4 (n=720) bad=4320 (cost 24); PSL(2,8) x C3 (n=756) bad=4536; S6 x C3 (n=720) bad=5760.
- Overall best with n > 684: bad = 4320 at n = 720 (A6 x C4, H order 4, exhaustive union search). No bad = 0 found.
- Capped union searches (8 files, tested = 300000) were NOT run through the SA mode (sa_capped.sh is ready but unused).
- The biregular idea (|H| != |K|, degrees (6, d_B)) was not run.
- Calibration: A3(2) Borel graph n=630, bad=0, verified by check.sh (apsp_ref OK).
