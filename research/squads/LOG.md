# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24, cell-12-8 (Opus, cloud session), round 1: (12,8), beat 4,650,100

Goal: a bipartite (12,8) graph above the table's 4,650,100 (Delorme 1985). Opus before the round: decoded the table
value as 2·35·|H(9)|, i.e. 7 × the (12,7) value 664,300 = Delorme's 5-level hexagon graph X_2 (same pattern at
Δ = 10, 11, 14, 16), so the target is a lift of "H(9) + 2 extra edges per vertex" by a group of order ≥ 36. Built
research/d12D8/tools (liftcheck scorer, nbwalks). Random voltages reach only order 12–14 at q = 9 (10 at q = 7, where
Delorme has 30); structured hop matchings raise the worst-case walk count from 6 to 25 but random second factors
still give ~1000 misses per source. Preamble: research/squads/d12D8_r1/CARD_COMMON.md.
Cards (squad A): c1 polychromatic point colourings as hop voltages · c2 apartment-holonomy voltages on H(9) alone
(far pairs) · c3 voltages from a 10-edge-colouring · c4 tripled-matching "bounce" designs · c5 sampled local search at
q = 9 · c7 non-abelian vs cyclic groups, random voltages · c8 literature (Delorme's construction) · c14 hard-target
analysis + rule. (squad B): c6 annealing calibration at q = 5 · c9 H(8) generator (q = 8, 3 hops, needs order 63) ·
c10 H(7) + 4 hops (needs order 119) · c11 route-chart lift feasibility at D = 8 · c12 dualities of H(9) (isometric
hops) · c13 GQ(11) incidence lifts (needs order 1589) · c15 wildcard · c16 star products (wildcard).

### Round 1 outcomes (reports so far; sampled = liftcheck STEP 331, 201 point sources; "full" = all sources)
- c1 polychromatic hops: no 7-colouring of H(9) with every line rainbow-complete found (best leaves 8,055 of 66,430
  lines short); hexagon-voltage-0 designs give 23k–129k misses/source (level 0 far lines); with random hexagon residues
  894/source at order 35. No gain over random.
- c2 apartment holonomy (H(9) alone): random voltages cover far lines up to order 5 only (N = 6: 27 sampled misses);
  q = 3 annealing reaches N = 2 exactly, stalls at N = 3; bilinear coordinate rules are random-like.
- c3 edge-colouring voltages: random-like; largest sampled-zero order 15 (1,992,900); 235 misses/source at 35.
- c4 tripled-matching bounces: largest sampled-zero order 17 (2,258,620; per-pair random copy voltages); 265
  misses/source at 35; constant copy voltages catastrophic (20–29k/source).
- c7 groups: order dominates; non-abelian groups tie cyclic ones of the same order (worse with many involutions);
  sampled-zero up to Z_13–Z_16.
- c9 H(8) generator (char 2; the polar row is needed in Tits' system): validated (girth 12, diameter 6). Random lifts
  of H(8) + 3 hops: sampled-zero at order 29–30 (2.17–2.25M).
- c10 H(7) + 4 hops: random Z_48 lift passes the full check: 1,882,368 vertices (valid, but far below the table);
  sampled checks are optimistic (N = 52 passed 203 sources, failed the full check).
- c11 route-chart lifts (3 letters × F_4): no cubic Haar controller of order ≥ 60 has exact-length-7 coverage
  (largest 50), so the (3,4) lift cannot reach m ≥ 142. Infeasible.
- c13 W(11) incidence graph (GQ, 12-regular): random Z_700 lift passes the full check, 2,049,600 vertices; misses
  follow 1464·m·e^(−14642/m); structured F_11³ voltages random-like.
- c14 hard targets: random designs miss in bulk (98% far lines, ~1 element each), not at a few hard targets.
- c15 pure H(11) lifts: impossible for any order ≥ 2 (each of the 1,464 lines within distance 3 of a point has one
  walk of length ≤ 7).
- Opus: random level-dependent Z_7 lifts of X_2 itself are no better than level-invariant ones (~900 misses/source);
  fixed "bounce" elements on tripled edges are catastrophic in every group (Frobenius F_9:Z_4 slightly better than
  random, 586 vs 670/source). SL(3,q) (torus, coordinate permutations, elementary matrices on (x0,x1,x2) with the dual
  action on (x4,x5,x6)) acts on hexgen's H(q) coordinates, so the Singer torus Z_91 (semiregular on points and lines
  of H(9), 730 orbits each) is available for symmetric designs.
- c6 q = 5 calibration: random voltages 0 misses up to N = 12; annealing (exact objective) reaches N = 16 (verified
  all sources, 124,992 vertices), N = 18 best 34, N = 20 best 191. Delorme has N = 25 at q = 5: search reaches about
  two thirds of the algebraic construction there, and less at q = 9 (16–17 of 35).
- Opus: affine twists x ↦ a·x + b on Z_N (Bermond–Delorme–Farhi style permutation lifts, tools/affcheck.c) behave
  exactly like random translations (N = 20: 0.15–0.18 misses per (p, x) source for translations, affine hexagon
  edges, all-affine); the star product of c16 (fibre cycles, even N) is in the same range (0.2/source at N = 20).
