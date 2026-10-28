# gqd5-r2 / c3: two-partner freed lines on a D->H arc (3-level test bed over Q(4,5))

Test bed: types D,H,H; arcs 0->1 (D->H, M = identity on lines, freed set R = lines), 1->2 (H->H), 2->0 (H->D, identity on
points, freed set = ovoid O of Q(4,5), 26 points).  Element ids: level-0 A = lines, level-1 A = points, level-2 A = points.

## Exact rule found

1. Bad pairs (verified). For a freed line l on arc 0->1 with partner lines m (meeting l at z), Theorem E (E2/E3 of
   repair.exact_conditions) fails exactly on the pairs (l, p) and (p', l) with p in m\{z} (q = 5 points) and p' the
   level-0 points of m\{z}. Check (2-pencil, z off O): E2 failure count 5 per line, E3 5 per line; brute_bad = 20 =
   2 lines x 5 points x 2 directions. A singleton (no concurrent freed line) has no failures. Two partners at distinct
   points z1 != z2 of l: the bad targets are (m1\z1) u (m2\z2).

2. One B-hub (slot of l in level 1 = one point w, repairs p iff d(w,p) <= 2) covers (m1\z1) u (m2\z2) only if w lies on
   both m1 and m2, impossible for z1 != z2 (no triangles). Tested: 0 of 300 random instances have any covering point.
   So a freed line may NOT meet two freed lines at different points.

3. Pencil of 2 {l,m} meeting at z: B-hub of l at a point w in m\{z} (level 1, freed on arc 1->2), B-hub of m at a point in
   l\{z}. A-hub of l sits at a level-0 point covering m\{z}, which must be the point O cap m (the unique ovoid point of m);
   the A-hub of m sits at O cap l. Both are distinct iff z is not on O. So a pencil meeting on the ovoid is FORBIDDEN.

4. Pencil of 3 {l,m1,m2} through z: each of the three needs a B-hub at z (the only point covering the other two lines'
   points) and an A-hub at z. So z needs three freed out-slots in its H-level and three freed in-slots at its D-level.
   In this 3-level bed each level has one out-arc and one in-arc (r = 1), so 3-pencils are impossible. Not tested in 7 levels.

5. Hub budget in this test bed. Each pair needs 2 B-hubs, each with a slot at a freed point of level 1, and level 1's only
   out-arc is H->H (non-friendly). Fact 4 allows at most 2 freed points there (local duality, q odd). So at most one pair
   is hub-repairable in the 3-level bed. (In a layout whose H-level has an H->D out-arc, the level-1 slot can be the ovoid
   point O cap m, see item 3; that is not available in the 3-level bed.)

## Sizes (max over line sets)
- Largest partial spread of Q(4,5) (pairwise non-concurrent): 18 (SAT finds 18; SAT at 19..22 timed out; annealing
  3 seeds gives 18). The Tallini bound is 21.
- Relaxed rule (items 1-3, pairs meet off O, no third line meets a pair), no hub-count cap: 23 = 6 pairs + 11 singletons
  (annealing, 4 seeds, all 23). Pairs <= 13 cap is not binding.
- Relaxed rule with exactly one pair: 18 (2 seeds) = the spread number, no gain.

## Built and checked (./research/theorems/d5gq/apsp EDGES 7 5)
- pencil_D5_valid_18.edges: pair + 16 singletons on arc 0->1, H->H arc = local duality on the 2 B-hub points
  (localdual.py), 2 B-hubs and 2 A-hubs, hub graph by hubopt.search. RESULT VALID d=7 D=5 n=940.
  Built with `LD=1 python3 pencil_build.py onepair18.json run18ld 0`.
- run23.edges: 6 pairs + 11 singletons (23 lines), 12 freed points on the H->H arc with a random bijection M12.
  INVALID (diameter 6). diag.py: every bad pair is between level 1 and level 2 (the H->H arc); none involves level 0,
  so the 6 D->H pencil repairs (A and B hubs) all work. The failure is the H->H arc, not the pencils.

## Score
- Test bed (valid graph): largest valid D->H set found = 18; largest partial spread = 18; score = 0.
- Rule-based (not built): 23 - 18 = +5 gain from pencils, assuming the H-level slot can be an ovoid point of the
  partner (needs an H->D out-arc at that level, as in the 7-level records).
