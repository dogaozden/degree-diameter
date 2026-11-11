# w1 NOTES (handsoff-49): Haar graphs of non-metacyclic groups, N = 2,486..2,700 (n = 2N)

Start: 2026-10-31 21:41 UTC. Planned end: 23:41 UTC. Last update: 23:01 UTC.

## Best result
- **A_7 (perfect, trivial centre, N = 2520, n = 5040): best cost 6 (diameter 10). No cost-0 Haar graph.**
- Exhaustive over ALL Haar graphs of A_7 (exh.c, every S up to inner automorphism and translation: S = {e, r, b, c},
  r = one representative of each of the 8 non-identity conjugacy classes, all b, c): min cost = 6, no zero.
  Costs seen: 6 (48+ sets per class), 12, and >= 7 for classes of reps 53 and 367 and 9. Files: w1/res/exh_A7_*.out.
  Cross-checked: cost function reproduces (0,0) for the known valid 4970 Haar graph; numpy cost and apsp agree on A7 sets.
- Near-miss edges: w1/t/A7_cost6.edges (S = {0,2348,2439,1235} in table indices, tabs/A7.bin; all three elements in the
  (3,2,2) class). apsp: diameter 10, far pairs 7560 (3 per vertex per side). Rebuild: `python3 tools/sol2edges.py
  w1/t/A7_r11.sol OUT.edges` (sol from `haar_tab_w1 4 9 60 11 8 OUT tab tabs/A7.bin 1` with SAVE_ANY=1).

## Other results (haar_tab annealing; cost = both sides; N = 2520..2700)
- Non-meta best families, floors 6-10 after 60-110 s: A7 6 (seeds 4, 11, 14; 12 for others); PGL(2,5)xZ21 7-8;
  PSL(2,8)xZ5 8; A5 x S3 x Z7 8 (4 s); PSL(2,7)xZ15 10; abc k15 (11:5:1,2:15:4) N 2640 10; abc k9 (2:3:2,73:9:1) N 2628 10;
  semi p5 k108 o12 (N 2700) 12; abc k32 (3:8,3:4) N 2592 14; PSL(2,11)xZ4 26; SL(2,11)xZ2 14; PSL(2,9)xZ7 13.
- Bad (cost >= 17): SL/PSL/PGL(2,7) x Z8/Z16 (20-77), AGL(1,q) x Z_n (15 to 2000), S4xZ105 406, SL(2,3)xZ105 1158,
  heis 3 x Z_n and heis 5 x Z_n (2100-3600), most abc with k=3 (2300+), AGL(3,2) x Z2 (56), AGL(2,3) x Z6 (17).

## What I learned
- Exact walk identity: diam(H(G,S)) <= 9 iff B4(S^-1 S) = G and B4(S S^-1) = G (B4 = radius-4 ball of the Cayley
  graph). Cost = uncovered counts of the two balls (cov.py, verified on the valid 4970 graph).
- The walks collide heavily: |B2(S^-1 S)| = 121 (not 145), so a random S has cost ~70 in A7 and the annealer's
  floor is structural, not a search failure (4 seeds: 6 or 12).
- Groups with a big abelian quotient or big centre are bad (heis, S4 x Z_n, AGL(3,2) x Z2). Perfect/trivial-centre
  groups (A7) do best among non-meta groups so far.

## Tools (w1/)
- cov.py (numpy cost for a table group), exh.c / exh (exhaustive class-rep scan; ~75 us per S, 3.2M S per class, about
  4 min per class), haar_tab_w1.c (haar_tab that saves the best S of a non-zero run when SAVE_ANY=1), drive.sh (batch
  screen), list_*.tsv (candidate lists), res/screen.tsv (all screen results).

## Next, in order
1. Exhaustive over S for a group with few conjugacy classes and trivial centre; only A7 fits in 2486..2700.
2. Non-meta groups of order 2486..2500 (none tested: 2486, 2488, 2490 have few non-meta candidates; check groups of
   order 2*3*5*83 = 2490 with a non-cyclic Z_83 action).
3. Surgery: start from the A7 cost-6 graph (n = 5040 is above 4970, but diameter 10 has 7560 far pairs).

## Final (23:05 UTC)
- A7 exhaustive is complete: classes 1,2,4,7,9,19,53,367 (non-identity reps), min cost 6, zero none.
  Logs: w1/res/exh_A7_class19.out, exh_A7_c01.out, exh_A7_c23.out, exh_A7_c67.out, exh_A7_c4.out.
- A5 x S3 x Z7 (centre Z7): 8, 8 at 60 s. PGL(2,5) x Z21: 8, 7, 8. PSL(2,8) x Z5: 8.
- Groups with trivial centre are the only ones that reached 6; A7 is the only one in range that is both perfect and
  centreless and small enough to scan exhaustively.

## Group properties vs cost (N 2520-2700; centre and abelianization from groups.py / abc.py facts)
| group | N | centre | G^ab (approx.) | involutions | best cost seen |
| A7 | 2520 | 1 | 1 | 105 | 6 (exhaustive min) |
| PGL(2,5) x Z21 | 2520 | 21 | 42 | 25 | 7 |
| PSL(2,8) x Z5 | 2520 | 5 | 5 | 63 | 8 |
| A5 x S3 x Z7 | 2520 | 7 | 14 | 63 | 8 |
| PSL(2,7) x Z15 | 2520 | 15 | 15 | - | 10 |
| abc k15 (11:5:1, 2:15:4) | 2640 | - | 15 | - | 10 |
| semi p5 k108 o12 | 2700 | - | - | - | 12 |
| heis 3 x Z_n, heis 5 x Z_n, S4 x Z105, AGL(3,2) x Z2 | 2500-2700 | >=2 | >=24 | - | 56-3600 |
Pattern: low cost goes with small centre and small abelianization; a big abelian factor (direct Z_n or Heisenberg-type
abelianization) is bad.
