# B5: ball-growth census on psl 243 x Z11 (k = 10 AFROBH, k = 10 AFROBD, k = 5 AFROB=3)

Status: complete for the 12 samples (RANDORB=4 LEVELS=4 per family, SEED 1). No solution, no search. The runs finished at
13:08, before the Opus session killed the running haar_sym processes at 13:24 (the cell was solved at 157,835,304), so
none of this card's processes were killed and none is left running.

## Setup

- Group G = psl 243 x Z11, N = |G| = 78,917,652 (each side of the Haar graph), D = 10, d = 11, mu = 60.61.
- Command shape: `haar_sym 11 10 60 1 8 /dev/null psl 243 11` with `RANDORB=4 LEVELS=4`, THREADS unset
  (OMP_NUM_THREADS=1). All three runs went through `gate.sh 480 bash B5/run_census.sh` (13:07:48 to 13:08:24, rc 0 for
  each). Raw logs: `B5/k10_afrobh.{out,err}`, `B5/k10_afrobd.{out,err}`, `B5/k5_afrob3.{out,err}`.
- Families:
  - k10H: `ORBIT="10 1 1" AFROB=1 AFROBH="0 1 2 0" AR=2`; alpha = conj by mat(0,1,2,0) after x -> x^3; |Fix| = 3 (+e).
  - k10D: `ORBIT="10 1 1" AFROB=1 AFROBD=1 AR=2`; alpha = conj by diag(1,-1) after x -> x^3; |Fix| = 1 (+e).
  - k5F3: `ORBIT="5 2 1" AFROB=3` (AR = 3 by default); alpha = x -> x^27 on entries with z -> 3z; |Fix| = 11 (+e).
  - AFROB=1 for the k10D family is my choice (the card does not give it); it matches k10H.
- Reading the levels: `lev[h]` is the cumulative count of distinct elements on the side reached at BFS step h (side B for
  even h, side A for odd h, with (e,A) counted in A). New distinct elements at BFS distance L are
  `lev[L-1] - lev[L-3]`, with lev[-1] = 1 (identity). Checks that passed on all 12 samples: lev[0] = 11 and
  cost = N - lev[8].
- Benchmarks: free = 11 * 10^(L-1) (non-backtracking words). Random model = uniform random S, with each side's words
  treated as independent uniform draws: N (1 - exp(-M/N)) for cumulative word counts M. Saturation starts at L = 7 for
  both benchmarks.

## Result: the level where k = 10 falls behind

Non-degenerate samples (cost < 1000): k10H s1, s2, s4; k10D s1, s2, s4; k5F3 s2, s3, s4. Degenerate samples: k10H s3
(cost 30,377), k10D s3 (cost 1,535,662), k5F3 s1 (cost 658). Table = mean new distinct elements over the 3 non-degenerate
samples of each family, with the lag against k5F3 in parentheses.

| L | side | free 11*10^(L-1) | random model | k10H | k10D | k5F3 |
|---|---|---|---|---|---|---|
| 1 | B | 11 | 11.0 | 11 | 11 | 11 |
| 2 | A | 110 | 110.0 | 110 | 110 | 110 |
| 3 | B | 1,100 | 1,100.0 | 1,100 | 1,100 | 1,100 |
| 4 | A | 11,000 | 10,999.2 | 10,953.3 (-40, -0.36%) | 10,993.3 (0) | 10,993.3 |
| 5 | B | 110,000 | 109,921.8 | 109,013.3 (-717, -0.65%) | 109,720.0 (-10) | 109,730.0 |
| 6 | A | 1,100,000 | 1,092,215.5 | 1,076,800 (-11,977, -1.10%) | 1,086,677 (-2,100, -0.19%) | 1,088,777 |
| 7 | B | 11,000,000 | 10,253,343.2 | 10,054,153 (-152,919, -1.50%) | 10,176,251 (-30,821, -0.30%) | 10,207,072 |
| 8 | A | 110,000,000 | 58,507,329.4 | 57,667,044 (-664,334, -1.14%) | 58,130,081 (-201,297, -0.35%) | 58,331,378 |

- k10H falls behind at **level 4**: all three non-degenerate samples are 20 to 60 short of 11,000, where k5 and k10D
  average 6.7 short. The lag grows to 0.65% at level 5 and about 1.1 to 1.5% at levels 6 to 8.
- k10D matches k5 through **level 5**. It falls behind only from level 6, by 0.2 to 0.35%.
- Level 3 is 1,100 for all 9 non-degenerate samples. The three degenerate samples are the only ones below 1,100
  (1,040, 1,040, 1,070), and their level-4 counts are 570 to 1,240 short. Count n3 < 1,100 flags them (3 of 3 flagged
  samples were degenerate; 0 of 9 unflagged were).
- Costs of the non-degenerate samples: k10H 101, 110, 90 (mean 100); k10D 62, 56, 70 (mean 63); k5F3 65, 45, 110 (mean 73);
  mu = 60.6. Only 3 samples per family, so these costs are descriptive only.

All 12 samples, degenerate ones included (`census_analyze.py` prints these): level 4 mean 10,665 (k10H), 10,685 (k10D),
10,853 (k5F3); level 8 mean 54.7M (k10H), 50.8M (k10D), 57.3M (k5F3). The degenerate samples (level-8 counts 28.7M,
45.8M and 54.2M) pull these means down.

## Raw BFS levels (from the .err files; lev0 ... lev8, then cost)

k10H (`ORBIT="10 1 1" AFROB=1 AFROBH="0 1 2 0" AR=2`):
```
11 111 1111 11051 109811 1083051 10109111 58554566 78917551 cost 101
11 111 1111 11091 110701 1096461 10269956 59157567 78917542 cost 110
11 111 1051 9911 92096 845791 7413391 46633602 78887275 cost 30377
11 111 1111 11051 109861 1084081 10113766 58552591 78917562 cost 90
```
k10D (`ORBIT="10 1 1" AFROB=1 AFROBD=1 AR=2`):
```
11 111 1111 11091 110451 1092001 10217983 59000415 78917590 cost 62
11 111 1111 11111 111001 1099911 10313891 59321756 78917596 cost 56
11 111 1051 9871 88906 667868 4383874 29318464 77381990 cost 1535662
11 111 1111 11111 111041 1101431 10329371 59361416 78917582 cost 70
```
k5F3 (`ORBIT="5 2 1" AFROB=3`):
```
11 111 1081 10541 102691 994336 9163586 55169988 78916994 cost 658
11 111 1111 11111 111041 1102796 10355656 59576087 78917587 cost 65
11 111 1111 11111 110896 1101036 10334656 59494601 78917607 cost 45
11 111 1111 11091 110586 1095811 10263427 59223090 78917542 cost 110
```

## Caveats

- Four samples per family, one seed. The lags at levels 4 to 5 (tens to hundreds of elements) are small and rest on three
  samples per family.
- All three runs use SEED 1, so the candidate orbits are probably shared across the two k10 families. Sample 3 has the
  same level-3 count (1,040) in both. The k10 families are not independent samples.
- The random model is a heuristic (words treated as independent uniform draws). It is only used for levels 4 to 8.
