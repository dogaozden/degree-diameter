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
