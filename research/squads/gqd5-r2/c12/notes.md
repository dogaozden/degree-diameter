# c12 wildcard (15,5): raising K_B above a+2c or K_A above b+2c

Result: no valid construction; score 0. Best possible from the H->D route is about +5 on K_B, not +41.

## Setting used
Typing HHHDHHD on the rotational 7-level tournament (j -> j+1, j+2, j+3). Arc caps: H->D = a, D->H = b, H->H and D->D = c.
K_B = a+2c and K_A = b+2c at the H-levels, which are the bottlenecks.

## 1. Non-uniform freed sets per arc: no gain
Every constraint is a sum of arc sizes, so the optimum sets each arc to its cap. Maximising over all typings and all
regular tournaments on 7 vertices gives min(a+b+4c, 3b+3c) (c15, formulas.md, r=3, exhaustive over the 3 classes).
At q=11, (a,b,c)=(122,70,2) this is a+b+4c = 200, far below 241.
So the target needs the caps themselves to rise: a+b+4c >= 241 with a <= 122 + small, b <= 111 (Tallini), c <= 3.

## 2. Freed POINT sets on H->D arcs above the ovoid (the wildcard idea)
- Friendly identity H->D: a freed set R must be a partial ovoid of Q(4,q) (Theorem, item 2) to be repaired inside its two levels.
- Two disjoint ovoids of Q(4,q) do not exist for q odd: every ovoid is an elliptic quadric section (Barlotti/Panella), and two
  hyperplane sections meet in a plane, which contains a singular point (Chevalley-Warning). SAT agrees at q=5
  (ovoids.py: UNSAT for an ovoid avoiding a given ovoid). So O1 u O2 on one arc is impossible; two ovoids on different arcs
  only help hub-hub collinearity (HG), not the cap.
- Counting bound for a relaxed set T of points (every point collinear with at most p other T-points):
  each line meets T in k_l points, sum_l (k_l - 1)_+ <= p|T|/2, and the lines meeting T number |T|(q+1) - sum_l (k_l-1)_+.
  Hence |T| <= (q+1)(q^2+1)/(q+1-p/2). For the pair rule p=1 this gives |T| <= 2(q+1)(q^2+1)/(2q+1):
  28 at q=5, 127 at q=11. So a = |T| <= 127 and K_A+K_B <= 127+70+8 = 205 at q=11 under the pair rule.
  Reaching 163 needs p >= 7 partners per point.
- Numerically at q=5: annealing for pair-rule sets (pairsa.py) found nothing above the ovoid (26), and adding one point
  to the ovoid (6 partners) gives 211 far level-level pairs (exp_hd.py). Larger p looks unrepairable, but this is not proven.

## 3. Hub feasibility (not the main obstacle, but blocks any prototype)
With the greedy index hub assignment and an annealed hub graph Y (degree q-3), the baseline ovoid/partial-spread build
(build_typed.py, c=0) does not reach HG at q=5 (206 bad hub pairs, delta=2) or at q=7 (115 bad, delta=4).
At q=3 (delta=0) the hub-hub far count is 52 with no Y. The lab's q=9 record needs delta=6.
So no small-q prototype of any H->D variant can be validated as a full graph with this search.

## Files
- hdlib.py: build with arbitrary H->D and D->H freed sets (uses levels.build); bad_pairs in python.
- reach.py: far pairs by boolean matrix powers.  exp_hd.py: far-pair split (level-level, hub-level, hub-hub).
- ovoids.py: SAT ovoid of Q(4,q) avoiding a given set.  pairsa.py: pair-rule annealing.
- edges/q5_ovoid_noY.edges: q=5 level graph plus hubs (26 B-hubs, 18 A-hubs), no hub graph. apsp INVALID (diameter 6;
  hub-hub pairs far). Reference only, not a record.
- T_*.json: point sets used in the tests.

## Projection
Best projection on this route: K_A+K_B <= 205 at q=11 (pair rule, a=127, b=70, c=2), not 241. Score 0 (no valid prototype).
Open: p >= 2 relaxed sets with a level-level repair (test at q=7, 9 with the exact two-level criterion); if such sets
reach 163 at q=11, K_B rises to 167 and the total to 245.
