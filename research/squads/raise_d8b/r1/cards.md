# raise-d8b round 1 cards (16). Each card: one strategy; rules in HEADER.md.

## c01 (17,8) PSL ladder, "3 5 2"
Climb (17,8) with PSL(2,p) x Z_n, ORBIT="3 5 2", haar_big0. Start at mu ~ 23 (e.g. psl 67 139, mu 23.4); on success
check, save, and step up mu by ~3 (`$GRP 17 8 25 34 3 30`, prefer 37 <= p <= 200 and n <= 300). If a rung stalls
(no gain for ~8 minutes), continue it once with START=OUT.best and a new SEED, else drop back.

## c02 (17,8) SL ladder, "3 5 2"
As c01 but SL(2,p) x Z_n only (the current record is SL(2,53) x Z139). Start near mu 24-26 (e.g. sl 59 103 is 27.9;
pick from `$GRP 17 8 22 32 3 40` lines starting "sl"), then climb.

## c03 (17,8) orbits of order 5, "5 3 2"
S = e + 1 fixed + 3 orbits of size 5 (ORBIT="5 3 2"); the (11,8) and (15,8) lab records used k = 5. Groups:
`$GRP 17 8 18 30 5 30` (p = +-1 mod 5, n's prime factors = 1 mod 5). First screen 3-4 groups with RANDORB=20 (median
cost), then search the best at mu ~ 21-24, then climb. Report whether k = 5 beats k = 3 at equal mu (compare with
RANDORB of ORBIT="3 5 2" on the same group).

## c04 (18,8) SL ladder, "3 6 0"
f = 0 (six free orbits, no e; right for 3 | d). The director runs PSL; you run SL(2,p) x Z_n only. Start at mu ~ 24
(sl 59 151), climb by ~3 per rung (`$GRP 18 8 24 40 3 40`, lines "sl").

## c05 (18,8) orbits of order 5, "5 3 3"
S = e + 2 fixed + 3 orbits of 5 (ORBIT="5 3 3"). Groups from `$GRP 18 8 15 30 5 30`. Screen with RANDORB=20 against
ORBIT="3 6 0" on the same group, then search the better one at mu ~ 20-25 and climb.

## c06 (18,8) small n shapes, "3 6 0"
Test the group shape with n tiny: PSL(2,p) and SL(2,p) with n = 1 (psl 397 1 is mu 27.7; find SL ones with `$GRP 18 8
20 40 3 60` and n = 1, 7, 13, 19). RANDORB=20 on 3-4 of them, then search the best at mu ~ 25-30.

## c07 (19,8) PSL ladder, "3 6 1"
The record shape (PSL(2,103) x Z79, mu 12.9). Start at mu ~ 19-20 (psl 71 247 is 18.8), climb by ~3 per rung
(`$GRP 19 8 18 34 3 40`, lines "psl", 37 <= p <= 250).

## c08 (19,8) SL ladder, "3 6 1"
As c07 with SL(2,p) x Z_n (e.g. sl 101 43 at mu 19.6, sl 113 31 at 22.7, sl 67 151 at 28.6).

## c09 (19,8) hole anatomy at D = 8 (analysis card, light CPU)
Run haar_big0 on psl 79 181 (mu 21.8), ORBIT="3 6 1", until it stalls at a small cost (or 12 minutes), then
`EVAL=OUT.best UNCPRINT=1` to list the holes. Classify each hole: alpha-fixed (commutes with g = [[0,-1],[1,-1]] up to
sign, and z fixed by r)? z = 0 layer? involution / order 3 / trace values? in the torus of g? Repeat on a second
stalled state (other seed or sl 113 31). Report the classes with counts and say what a fix would target. Save notes in
your folder (holes.md).

## c10 (20,8) PSL ladder, "3 6 2"
The record shape (PSL(2,71) x Z343). Start at mu ~ 19-20 (psl 109 97 is 18.8, psl 107 103 is 20.2), climb by ~3
(`$GRP 20 8 18 34 3 40`, lines "psl"). Evaluations cost ~2x those at (18,8).

## c11 (20,8) orbits of order 5, f = 0: "5 4 0"
20 = 4 x 5: four free orbits of size 5, no e (the (15,8) record recipe was k = 5, f = 0). Groups from
`$GRP 20 8 15 30 5 30`. Screen RANDORB=20 against "3 6 2" on the same group; search the better at mu ~ 20, climb.

## c12 (20,8) SL ladder, "3 6 2"
As c10 with SL(2,p) x Z_n (e.g. sl 61 277 mu 19.0, sl 67 211 mu 22.1, sl 61 283 mu 26.7).

## c13 (19,8) or (20,8): other group families with haar_sym (wildcard family)
haar_big0 only does SL/PSL(2,p) x Z_n. haar_sym also does `prod sl q1 sl q2 n`, `sl 2^k poly ...`, `pgl q n`
(research/structured/README.md; (13,8) was raised with prod sl 7 sl 7 n 31 and with sl 64 poly x^6+x+1 n 13). Pick
groups of order N with mu ~ 18-24 at (19,8) (N ~ 4.4e7-4.5e7; W from research/frontier/beyond/plan.py), screen with
RANDORB, search the best with ORBIT="3 6 1". haar_sym prints the solution like haar_gen3; check it with haarcheck_gen.

## c14 (19,8) group-shape tournament (screening card)
At equal mu ~ 24 (+-1), compare shapes by RANDORB=30 (median and min cost) with ORBIT="3 6 1": PSL n = 1, PSL with
n ~ 7-31, PSL with n ~ 100-300, PSL with n ~ 1000+, and the same for SL. Then give the two best shapes 4 minutes of
search each and the worst one 4 minutes. Report a table: shape, group, median RANDORB cost, best cost after search.

## c15 Near-miss finisher at (18,8)
The director's runs save their best S in
/home/user/degree-diameter/research/frontier/raise_d8/runs/d18D8_psl_79_127_orb3-6-0_s1.sol.orb and
.../d18D8_psl_61_283_orb3-6-0_s1.sol.orb (orbit form, ORBIT="3 6 0", group psl 79 127 / psl 61 283; copy them to your
folder first, never write there). If one of them is still at cost > 0, try to finish it: START=<copy> with other seeds,
larger K (16, 32), TARGP=90, TMAX=0.5 (a cold restart near the state), and also UNCPRINT on the state to see which holes
remain. Report what finishes near misses (or that nothing does).

## c16 Wildcard: an approach none of the other cards uses
Other cards: PSL/SL x Z_n ladders with k = 3 at all four cells, k = 5 orbits at (17,8), (18,8), (20,8), n = 1 shapes,
haar_sym families (prod, GF(2^k), pgl), shape tournament, hole anatomy, near-miss finishing. Find something different
that could give a larger diameter-8 graph at d = 17..20 (a different construction, group family, automorphism, or a way
to reuse a smaller graph), test it at small scale within the time box, and report whether it could beat the current
values (with numbers). If it produces a graph, it must be checked (haarcheck_gen for Haar graphs; for an edge list use
research/lifts/coordinator_check/apsp.c, build it with cc -O3 -fopenmp).
