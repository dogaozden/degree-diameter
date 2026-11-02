### D = 9 at Δ = 17..20, raised (job raise-d9, 2026-11-01/02)

Job raise-d9 (Opus director + four Haiku squad rounds of 16-17 cards, cloud session, branch
claude/raise-d9-orbit-metacyclic-ndvfty). Goal: raise every D = 9 value at Δ = 3..20 with the orbit and
metacyclic/Frobenius searches of beyond-d11 and beyond-d11b. Tools: research/frontier/beyond11/haar_big0.c and the new
research/frontier/raise9/haar_big1.c (haar_big0 plus FIXF at D = 9, below); queue and check scripts research/frontier/raise9/
(dq.sh, chk.sh, cells9.txt, rows9.py); search logs runs/, check logs checks/, squad work research/squads/raise9/r1..r4/.

**Where the room was.** In size-law terms (mu = N exp(-W/N), SIZE_LAW.md) the D = 9 values at Δ <= 16 already sat at mu 23-47
(earlier orbit-search jobs pushed them hard), but the four new cells (17..20, 9) of new-cells-beyond sat at mu 2.6-2.9 (first S
solved). haar_big0 evaluates an orbit S of SL(2,p) x Z_n at N = 2.7e8 in about 0.2 s with 2 threads (1e9 in about 2.5 s), so
these cells could be pushed up the mu ladder.

**Results (all haarcheck_gen VALID from (e,A) and (e,B); solution files research/frontier/sols/, check logs
research/frontier/raise9/checks/):**

| cell | was | first rung (mu) | now (mu, evaluations) | gain |
|---|---:|---|---|---:|
| (17,9) | 501,707,400 | 543,962,400 SL(2,151) x Z79 (13.2) | **549,370,752** SL(2,97) x Z301 "3 5 2" (15.7, 2,639) | +9.5 % |
| (18,9) | 790,626,816 | 850,056,960 SL(2,191) x Z61 (11.35) | **867,712,560** SL(2,131) x Z193 "3 5 3" (16.5, 229) | +9.7 % |
| (19,9) | 1,218,394,320 | 1,317,726,672 SL(2,277) x Z31 (13.4) | **1,328,920,800** SL(2,151) x Z193 "3 6 1" (15.7, 17) | +9.1 % |
| (20,9) | 1,823,175,864 | 1,972,000,272 SL(2,373) x Z19 (12.5); 1,993,145,280 SL(2,239) x Z73 (15.35) | **1,998,558,432** SL(2,233) x Z79 "3 6 2" (16.2, 57) | +9.6 % |

**What decided the shape: torus holes.** ODD_D_HOLES.md (beyond-d11) predicted that at odd D the extra holes are -I, the 2n
central elements (+-I, z) and the ~p alpha-fixed torus elements, and recommended SL(2,p) x Z_n with small n. At D = 9 the
first rungs (mu 12.5-13.4) solved with that shape, but every push above mu ~17 with large p and small n (SL(2,277) x Z13,
SL(2,313) x Z9, SL(2,457) x Z7, SL(2,523) x Z7) stalled at cost 2-30. EVAL + UNCPRINT of the cost-2 plateaus (SL(2,277) x Z13
and SL(2,139) x Z103 at (17,9)) showed an inverse pair of alpha-fixed TORUS elements a I + b g, z = 0, each time; squad card
r3/w07 found no central holes in 6 sides where the clump model predicted ~9. So the director switched to small p (97-233) and
large n with gcd(r - 1, n) = 1 (only z = 0 alpha-fixed): (19,9) SL(2,151) x Z193 at mu 15.7 solved in 17 evaluations, (20,9)
SL(2,233) x Z79 at mu 16.2 in 57, (18,9) SL(2,131) x Z193 at mu 16.5 in 229, (17,9) SL(2,97) x Z301 at mu 15.7 in 2,639. Very
small p is bad again (r4/p4: SL(2,53) x Z1867 stalled at 78): short relations in small SL(2,p) (FROBENIUS.md, r2/h13).
ORBIT split: the fewest fixed generators gave the best random statistics (r3/w07, s18, s19: (18,9) "3 6 0" < "3 5 3" <
"3 4 6"; (19,9) "3 6 1" < "3 5 4" < "3 4 7"), but at (18,9) the solves came with "3 5 3".

**haar_big1: FIXF at D = 9.** haar_big0's FIXF screen (fully evaluate only candidate orbits that leave no alpha-fixed hole)
existed for D = 10 only. haar_big1.c adds the odd-D test: an alpha-fixed x is within 8 of (e,A) iff v x is in
X_4 = S^-1 S S^-1 S for some v in X_4 (one v per alpha-orbit), and the same with Y_4 = S S^-1 S S^-1 for side B. Validated
against the full evaluation on five states (2 of 2, 0 of 0, 0 of 6, 0 of 6, 0 of 6 alpha-fixed holes; 0.06-0.34 s per screen).
RESULTS_FIXF

**Inside the 2013 table (Δ <= 16): no raise.** Squad rounds 1-4 (65 cards, research/squads/LOG.md) tried: SL(2,p) x Z_n with
small n at (8,9), (9,9), (11..14, 9) (worse at (13,9), at par elsewhere; best near misses cost 9-12); odd-order Frobenius
groups Z_p x| Z_k at (6,9) (random-S statistics 2x better than SL(2,17) x Z13, cost 2 on 3 of ~170 fresh seeds of Z1559 x|_84
Z41 and Z2551 x|_7 Z25, never 0), (7,9) (cost 16), (8,9) (18), (9,9) (24); products with a Frobenius factor; orbit order 5
at (10,9)-(16,9) ((15,9) PSL(2,151) x Z61 "5 3 0" cost 4 at N just above the bar; no edge in random medians elsewhere);
field-automorphism orbits at (8,9)/(9,9); product groups at (12,9); a twisted product Z173 x| PGL(2,29) at (10,9);
single-orbit S (exhaustive over the representative) at (5,9)-(7,9); lifts of a 2+2 base and odd non-metacyclic groups at
(4,9) (best cost 24 and 28); bi-coset graphs for (3,9) (weak negative).
- (3,9): exhaustive cubic Haar search over 2,191 groups of order 254-330 and ~690 metacyclic groups of order 331-360 (r1/a02):
  no diameter-9 graph; min cost 8 at N = 272 (Z17 x| Z16); cost 0 only at N = 253 (Z23 x| Z11 = the 506 value itself).
- Covers (r3/w09): a regular cover of a solved D = 9 Haar graph never has diameter 9: every solved base has a same-side vertex
  reached by exactly one non-backtracking walk of length <= 8, so in an M-fold regular cover the other M - 1 lifts of it are at
  distance > 8 from the lift of the start.
Why these cells did not fall: the values at Δ <= 16 sit at mu 23-47, where the orbit search of earlier jobs already ran for
hours per cell; the squads' cards got ~1/10 core each on this 4-core machine (load ~20), i.e. 90-300 evaluations per card,
and the near misses were generic holes (no alpha-fixed ones) that more search, not a screen, would have to remove.
