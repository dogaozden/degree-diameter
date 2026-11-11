# r2c: cost-0 Haar sets for split metacyclic groups of order 2,440..2,485 (d >= 8)

## What was run
- `list_meta.py` -> `cands.json`: split metacyclic Z_m x|_r Z_k with m*k in 2440..2485, r^k = 1 mod m, d = ord(r mod m) >= 8,
  r deduplicated under r ~ r^t (gcd(t,k)=1), |G/G'| = k*gcd(r-1,m) <= 309. 46 groups, all kept. `groups.json` lists them.
- `driver.py` (resumable, state in `state.json`): per group `tools/mkmeta.py m k r KEY`, exhaustive check of every
  automorphism generator (kept only the passing ones), then `hx KEY.tab KEY.aut 0 9 XFROM XTO KEY.hits` in chunks of 12
  x-representatives (reps 1..K, K = x-orbits printed by hx). Stops a group at the first cost-0 set and verifies it with
  `tools/apsp EDGES 4 9` (must be VALID) and `tools/apsp EDGES 4 8` (must be INVALID). One line per group in
  `r2/scoreboard.jsonl` (card "r2c").
- `hx` is `tools/hx.c` compiled unchanged (`gcc -O3 -march=native -o hx hx.c`).
- `list_sg.g` (GAP): SmallGroups of orders 2440..2485 with |G/G'| <= 309, metacyclic test (some class representative c with
  <c> normal and G/<c> cyclic) -> `sg_list.txt`. Classifier sanity-checked: C2^3, A4, SmallGroup(8,5) non-metacyclic;
  D8, Q8 x C3, C2 x D10 metacyclic.
- `iso6.g` (GAP IsomorphismGroups): the 6 pairs of listed groups with equal order distribution and centre size are all
  isomorphic (so 46 listed groups = 40 distinct groups).

## Results (score 0 = cost-0 Haar set exists; ">0" = exhaustive hx LIMIT 0, none)
- N = 2485: Z_71 x|_2 Z_35 (d 35) = the record group (2 = 12th power of 49 mod 71): 0. S = {0,71,924,1358}, apsp VALID n=4970.
- N = 2440: Z_61 x|_8 Z_40 (d 20): 0. S = {0,122,550,1589}, apsp VALID d=4 D=9 n=4880, INVALID at D=8. Edges: `g2440_61_40_8.edges`.
- N = 2440, other 6 groups: >0 (Z_122 x|_23 Z_20 d20; Z_61 x|_3 Z_40, Z_122 x|_3 Z_20, Z_244 x|_3 Z_10, Z_244 x|_41 Z_10,
  Z_244 x|_95 Z_10 with d 10).
- N = 2448 (15 groups, d 16 and 8): all >0. N = 2460 (11 groups, d 20 and 10): all >0. N = 2480 (12 groups, d 10): all >0.
- Consistency: the isomorphic pairs (6 pairs) gave identical results.
- SmallGroups: 29 library groups with |G/G'| <= 309 in orders 2445..2485 (the orders 2440, 2442, 2444, 2448, 2450, 2456,
  2457, 2460, 2464, 2466, 2470, 2472, 2475, 2478, 2480, 2484 are not in the library); all 29 are metacyclic, so none is
  in scope. Not run.

## Not covered (outside the card's d >= 8 scope)
- split metacyclic with d in 3..7 and |G/G'| <= 309: 152 candidates (before isomorphism dedup). To list them, replace the
  filter `if d < 8: continue` in `list_meta.py` by `if d < 3 or d > 7: continue` (not run here).
- metacyclic SmallGroups with d < 8 or non-split; non-metacyclic groups of the 16 orders not in the library.

## How to rerun
- All groups: `cd r2/c && BUDGET=80 timeout 100 nice -n 10 python3 driver.py` (repeat until "done 46/46").
- One group by hand: `python3 ../../tools/mkmeta.py 61 40 8 g2440_61_40_8; ./hx g2440_61_40_8.tab g2440_61_40_8.aut 0 9 1 31 g2440_61_40_8.hits`
  (K = x-orbits printed on stderr; a `MIN 0` line means a cost-0 set exists).
- Tables for the groups marked ">0" were deleted to save disk (about 12 MB each); mkmeta rebuilds them in seconds.
