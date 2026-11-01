# w10 NOTES (handsoff-49): Haar graphs of centreless groups with small abelianization

Start: 2026-10-31 23:13 UTC. Planned end: 01:15 UTC. Last update: 00:38 UTC.

## Best result
- **S5 x (Z7 x| Z3) = S5 x F21 (order 2520, n = 5040, centreless, |G^ab| = 6): best cost 8** (every seed and K=4, 8, 16:
  seeds 1, 2, 11, 12, 13, 21; floor is structural). No valid Haar graph. Set S = [0, 1840, 988, 1705] (table indices).
  apsp on runs/S5xF21_cost8.edges: diameter 10, far pairs 10080. Scoreboard line written (00:25).
- No group in this card reached cost <= 4, so the exhaustive search (cards: cost <= 4 rule) was not triggered.

## Screen (haar_tab, table groups, N = 2n/2; 60 s per run unless noted; screen.tsv has every run)
| group | N | ab | best cost (seeds) | structure |
| S5 x F21 (S5 x (Z7:Z3)) | 2520 | 6 | **8** (x6 seeds, 120 s x3) | nonsolvable, centre 1 |
| Z3^5 : Z11 | 2673 | 11 | 22 (3 seeds + 120 s x2) | Frobenius, abelian normal V |
| A5 x AGL(1,7) | 2520 | 6 | 25 (2 seeds + 120 s x2) | |
| Z17^2 : Z9 | 2601 | 9 | 28 (2 seeds) | Frobenius |
| ASL(2,5) = Z5^2 : SL(2,5) | 3000 | 1 | 50 (3 seeds) | perfect |
| (Z7:Z3) x (Z13:Z12) | 3276 | 36 | 62 (3 seeds) | |
| Z11^2 : SL(2,3) | 2904 | 3 | 68 (3 seeds) | |
| Z29^2 : Z3 | 2523 | 3 | 2296 (2 seeds, same value) | Frobenius; floor is huge, checked (fresh start 3554) |
| Z19^2 : Q8 | 2888 | 4 | 507 (3 seeds) | |
| S5 x D11 | 2640 | 4 | 150 (2 seeds) | |
| A5 x D21 | 2520 | 2 | 174 (2 seeds) | |
| Z2^8 : D5 | 2560 | 2 | 210 (1 seed) | |
| Z3^3 : (GL(2,3) x Z2) | 2592 | 4 | 61 (1 seed) | |
| S4 x AGL(1,11) | 2640 | 20 | 33 (1 seed) | |
| Z37^2 : Z2 | 2738 | 2 | 4858 (1 seed) | |
| Z2^8 : Z10 | 2560 | 10 | 100 (1 seed) | |
| Z11^2 : D11 | 2662 | 22 | 67 (1 seed) | |
| Z19^2 : D4 | 2888 | 4 | 344 (1 seed) | |
| Z19^2 : Z8 | 2888 | 8 | 262 (1 seed) | |

Pattern: the nonsolvable groups (S5 x F21 = 8, A7 = 6 from w1) are the only ones near the bottom. Solvable groups with an abelian
normal subgroup of small index (Frobenius, V x| H with H small, dihedral factors) sit at 22-2296. Direct products with dihedral
factors are bad (D11, D21 factors: 150-174).

## Tools (w10/)
- mk.py: group toolkit (semidirect_vec over GF(p), props: centre, |G'|, abelianization; write_bin).
- build1.py, build2.py, build3.py: table builders for the lists above (tabs/NAME.bin).
- screen.sh SECS "SEEDS" NAME...: runs haar_tab on tabs/NAME.bin, appends to screen.tsv.
- runs/S5F21_sav.sol: best S of the S5 x F21 run (w1's haar_tab_w1 with SAVE_ANY=1); runs/S5xF21_cost8.edges.

## Next ideas (not done)
1. Exhaustive over all S of S5 x F21 up to conjugation (35 conjugacy classes x about 3.2M sets, with the 8 us cost of haar_tab's
   evaluator instead of w1's 75 us): about 1 h of CPU. It would settle whether 8 is the true minimum for this group.
2. Non-solvable centreless groups of order 2486..2700 that are not direct products with a dihedral or Frobenius factor (search
   for groups of the form V x| H with H nonsolvable acting without fixed points); AGL(2,4) (order 2880) is the next to test.
3. Surgery on the S5 x F21 cost-8 set: 2-switch moves from the far-pair list (far pairs 10080 is large, so probably a dead end).
