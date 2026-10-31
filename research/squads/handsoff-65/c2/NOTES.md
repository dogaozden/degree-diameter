# c2 notes (handsoff-65): lifts of bigger bases (p+p, p = 3..8) by small groups, tabu

Target: 6-regular bipartite lift with n = 2pm > 684 and diameter 5 (bad = 0).

## Setup (done)
- `mkbase.py P MODE SEED OUT`: random 6-regular bipartite multigraph base on p+p vertices, tabu format.
  MODE full = J + (6-p) random permutations (every side pair adjacent, many 4-cycles); MODE rand = 6 random permutations.
- groups: `groups/sg_<order>_<i>.txt` exported with `gap -q -c 'ORDER:=m; OUTDIR:="groups";' ../shared/gap_tables.g`
  (exported orders 43-45, 49-51, 58-60, 69-72, 80, 86-90, 115-120). `mkcyc.py M OUT` writes cyclic C_M.
- `scan.py P MODE BASESEED SECS OUT.tsv GROUPS...`: one random base per group, tabu SECS seconds (INIT=random),
  appends one line per group to OUT.tsv (cols: p mode baseseed m group best steps secs).
- Speed: tabu does about 10 steps/s at p=4 (17 free edges x m values per step, 8 DFS sources); vl (SA) does about
  8000 iterations/s and reached similar costs.

## Results so far
- Calibration: p=3 full base, C80 (N=480): cost 0 quickly. p=4, C80 (N=640): cost 13 after 20 s. p=3 cyclic groups
  C100 (N=600) cost 7, C115 (N=690) cost 32 in 25 s: abelian groups look bad at N near 690.
- p=3, m=116..119 (N=696..714), 8 s screens: best 24 (C29:C4 and C58xC2 at 696), 30 (C3x(C13:C3)? at 702).


## Screens batch 1 (scan.py, one random 'full' base per group, short tabu runs)
- p=3, m=120 (N=720), 8 s, 47 groups: best 32 (sg_120_14).
- p=3, m=116..119 (N=696..714), 8 s: best 24 (C29:C4), 30..36 for the rest.
- p=4, m=86..90 (N=688..720), 15 s, 26 groups: best 42 (C11:C8 = sg_88_1, and D43 side: C86 sg_86_2 at 42).
- p=5, m=69..71 (N=690..714), 10 s: best 56 (C69).
- Reading: costs fall slowly with time; tabu at p>=4 is ~10 steps/s, so 8-15 s screens are weak evidence.
- Note: 'full' mode only works for p <= 6 (row sums); added mode 'kminus' (K_{p,p} minus p-6 disjoint permutations)
  for p = 7, 8.

## Screens batch 2 (run_scans2.sh): p=6 m=58..60 (full = K_{6,6}), p=7 m=49..51 (kminus), p=8 m=43..45 (kminus), p=5 m=72.

## Screens batch 2 results (10 s / 8 s runs)
- p=6 m=58..60 (K_{6,6} base): best 69 (C58? sg_58_2 = D29), 94 for 59.
- p=7 m=49..51 (kminus base): best 90. p=8 m=43..45 (kminus): best 130 (only ~22 steps: too few to converge).
- p=5 m=72 partially run (killed).
- Trend: at equal (short) time, cost rises with p because each tabu step scans all free edges x m values and
  evaluates b DFS sources, so bigger p gets fewer steps.

## Long runs (540 s, export via export_c2.py, scored by shared/check.sh)
- p=3 full base seed 101, C29:C4 (sg_116_2), N=696: cost 20 (from 24 in the screen), 4819 steps.
  Exported lift: c2/long/p3_116_C29C4_lift.edges (copy c2/best696.edges). bad = 1160 far pairs
  (orbit cost x m / 2). Scoreboard line added.
- Cost-to-bad conversion: far unordered pairs ~ cost * m / 2 (each orbit has m pairs, counted from both ends).

## Base-class sweep (in progress)
- enum3.py: 18 classes of 3x3 multiplicity matrices (row/col sums 6, connected) -> bases/class3_k.base; class_sweep.sh
  runs each for 60 s with C29:C4 (results in classes.txt).
