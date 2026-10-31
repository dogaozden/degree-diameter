c7 (wildcard): focused neighbourhood for the fsd tabu.
Code: /home/user/degree-diameter/research/squads/sd5c-r1/c7/fsd_focus.c (copy of fsd.c; compiled to fsd_focus).
Idea: with probability FOCUS% per candidate, pick a random uncovered element z of G (not in XX) and propose
s' = s_l z^-1 s_i^-1 s_j or s' = s_l s_j^-1 s_i z (i,j,l random indices of S), which would create a product covering z;
the proposal replaces a random item of the same type (psi-fixed / orbit); exact energy decides.
Runs:
 calibration meta 251 20 32 1 (K=13, TYPES=1,3, SECS=60, FOCUS=50, SEED=1): records 0 and 1, f=1: best 36 and 32 (no solution,
   stopped by me after 2 of 6 records for time reasons; plain fsd solves this group in ~83 s).
 meta 61 96 21 1 (5,856), TYPES=1,3, FOCUS=50: records 0 and 1, f=1: best 104 and 110 (Opus plain best 20 over all records/types).
Steps per second are ~430 vs plain (not measured under same load); each focus step costs a full XX rebuild (~25k products).
