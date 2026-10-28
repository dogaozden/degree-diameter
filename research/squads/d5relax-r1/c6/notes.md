# c6: algebraic families (wildcard), squad d5relax-r1

Script: `families.py q 300` (300 samples per random family). For each sampled point set S: raw size; "thin" = greedily delete the point with the most collinear partners inside the set until the set is relaxed (best of 6 runs, random tie-breaks); "aug" = thin, then greedily add points that keep the set relaxed. Columns: sets; raw median; thin max (median); aug max (median).

## q = 5

| family | sets | raw med | thin max (med) | aug max (med) |
|---|---|---|---|---|
| A1 graph f quadratic (q^2 pts) | 300 | 25 (max 25) | 14 (13) | 23 (20) |
| A2 graph f quad + infinity g quad (q^2+q) | 300 | 30 (max 30) | 17 (14) | 23 (20) |
| A3 graph f cubic + infinity g cubic | 300 | 30 (max 30) | 17 (14) | 23 (20) |
| B1 random quadric Q=0 | 300 | 31 (max 56) | 18 (13) | 23 (20) |
| B2 elliptic x0x1+x2^2-n x3^2 | 1 | 26 (max 26) | 12 (12) | 20 (20) |
| B2 hyperbolic x0x1+x2x3 | 1 | 36 (max 36) | 12 (12) | 12 (12) |
| B2 cone x0x1+x2^2 | 1 | 31 (max 31) | 13 (13) | 20 (20) |
| C1 Q1=0 & chi(Q2)=-1 | 300 | 13 (max 50) | 20 (9) | 23 (20) |
| C2 Q1=0 & chi(Q2)=+1 | 300 | 13 (max 35) | 18 (9) | 23 (20) |
| C3 chi(Q1)=e1 & chi(Q2)=e2 | 300 | 23 (max 45) | 18 (12) | 23 (20) |
| D1 chi(N(a-lam b))=e (lam in F_q^2) | 50 | 75 (max 75) | 20 (19) | 23 (23) |
| E1a Sp-translate of twisted cubic | 300 | 6 (max 6) | 6 (6) | 22 (19) |
| E1b Sp-translate of conic | 300 | 6 (max 6) | 6 (6) | 23 (20) |
| E2 greedy union of Sp-translates of cubic/conic | 5 | 12 (max 12) | 12 (12) | 20 (20) |

## q = 7

| family | sets | raw med | thin max (med) | aug max (med) |
|---|---|---|---|---|
| A1 graph f quadratic (q^2 pts) | 300 | 49 (max 49) | 26 (20) | 41 (34) |
| A2 graph f quad + infinity g quad (q^2+q) | 300 | 56 (max 56) | 26 (22) | 40 (33) |
| A3 graph f cubic + infinity g cubic | 300 | 56 (max 56) | 26 (23) | 37 (33) |
| B1 random quadric Q=0 | 300 | 57 (max 106) | 26 (22) | 40 (34) |
| B2 elliptic x0x1+x2^2-n x3^2 | 1 | 50 (max 50) | 22 (22) | 35 (35) |
| B2 hyperbolic x0x1+x2x3 | 1 | 64 (max 64) | 16 (16) | 27 (27) |
| B2 cone x0x1+x2^2 | 1 | 57 (max 57) | 21 (21) | 30 (30) |
| C1 Q1=0 & chi(Q2)=-1 | 300 | 24 (max 70) | 28 (14) | 38 (32) |
| C2 Q1=0 & chi(Q2)=+1 | 300 | 24 (max 98) | 28 (14) | 38 (31) |
| C3 chi(Q1)=e1 & chi(Q2)=e2 | 300 | 71 (max 114) | 32 (25) | 39 (34) |
| D1 chi(N(a-lam b))=e (lam in F_q^2) | 98 | 196 (max 196) | 36 (32) | 41 (38) |
| E1a Sp-translate of twisted cubic | 300 | 8 (max 8) | 6 (6) | 36 (31) |
| E1b Sp-translate of conic | 300 | 8 (max 8) | 8 (8) | 37 (33) |
| E2 greedy union of Sp-translates of cubic/conic | 5 | 8 (max 16) | 16 (8) | 35 (34) |

## q = 11

| family | sets | raw med | thin max (med) | aug max (med) |
|---|---|---|---|---|
| A1 graph f quadratic (q^2 pts) | 300 | 121 (max 121) | 48 (40) | 78 (63) |
| A2 graph f quad + infinity g quad (q^2+q) | 300 | 132 (max 132) | 50 (41) | 74 (63) |
| A3 graph f cubic + infinity g cubic | 300 | 132 (max 132) | 47 (42) | 67 (62) |
| B1 random quadric Q=0 | 300 | 133 (max 254) | 51 (42) | 78 (64) |
| B2 elliptic x0x1+x2^2-n x3^2 | 1 | 122 (max 122) | 39 (39) | 66 (66) |
| B2 hyperbolic x0x1+x2x3 | 1 | 144 (max 144) | 24 (24) | 57 (57) |
| B2 cone x0x1+x2^2 | 1 | 133 (max 133) | 37 (37) | 56 (56) |
| C1 Q1=0 & chi(Q2)=-1 | 300 | 61 (max 231) | 46 (29) | 68 (60) |
| C2 Q1=0 & chi(Q2)=+1 | 300 | 61 (max 176) | 46 (29) | 71 (60) |
| C3 chi(Q1)=e1 & chi(Q2)=e2 | 300 | 297 (max 550) | 70 (52) | 74 (65) |
| D1 chi(N(a-lam b))=e (lam in F_q^2) | 242 | 726 (max 726) | 64 (59) | 74 (68) |
| E1a Sp-translate of twisted cubic | 300 | 12 (max 12) | 8 (8) | 65 (58) |
| E1b Sp-translate of conic | 300 | 12 (max 12) | 12 (12) | 69 (61) |
| E2 greedy union of Sp-translates of cubic/conic | 5 | 12 (max 24) | 24 (12) | 67 (64) |

## Extension with rtabu (q = 11, 180 s each, seed 1)

| seed family | seed size (aug) | rtabu best | file |
|---|---|---|---|
| A1 graph (1,x,y,f), f quadratic | 78 | 89 | rt_A1.txt |
| B1 random quadric Q=0 | 78 | 89 | rt_B1.txt |
| C3 chi(Q1)=e1 & chi(Q2)=e2 | 74 | 89 | rt_C3.txt |

best.txt = rt_A1.txt, score.py: size 89, pairs 36, valid true. Each run reached 89 within 4 s and did not improve after that.

## Baseline and reading

- Plain random-order greedy maximal relaxed sets at q=11 (40 trials, no family): max 65, median 58.
- Family seeds plus augmentation reach 78 at q=11 and 41 at q=7 (known best 41), 23 at q=5 (known best 23).
- Thinning of the large algebraic sets (q^2 to q^3 points) leaves only 20-50 points; the final size is mostly set by greedy maximal extension. Small Sp-translate seeds (8-12 points) reach 65-69 after augmentation, so the seed matters less than the search.
- Quadric zero sets: elliptic (aug 66), hyperbolic (57) and cone (56) at q=11 were weaker than random quadrics (78). For odd q the polar form of a quadric is symmetric, not the symplectic form of W(q), so these sets are not independent sets and need thinning.
- Norm conditions chi(N(a - lam b)) = e (lam in F_{q^2}) gave aug 74 with 726-point sets (thin 64).
- No family or seed reached 111; the best q=11 relaxed set found here is 89, the same as the known best.

