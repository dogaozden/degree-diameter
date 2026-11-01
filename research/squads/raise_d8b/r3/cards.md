# raise-d8b round 3 cards (16). Rules in HEADER.md. Search cards: for each candidate run
# `ORBIT="k m f" RANDORB=16 THREADS=1 nice -n 10 timeout 100 $BIN/haar_big0 d 8 60 1 8 /dev/null fam p n` (one at a time),
# read min and median from the "RANDORB d=..." line, compute median/k, then search the candidate with the lowest
# median/k: `nohup env ORBIT="k m f" THREADS=1 nice -n 10 $BIN/haar_big0 d 8 1400 SEED 8 a.sol fam p n > a.log 2>&1 &`.
# Poll with `sleep 100; tail -n 1 a.log`. Check any a.sol with haarcheck_gen. Do not kill the run early.

## e01 (17,8), mu ~ 40: "5 3 2" psl 41 631 | "5 3 2" psl 61 191 | "7 2 3" psl 41 631
## e02 (17,8), mu ~ 47-51: "5 3 2" psl 29 1801 | "5 3 2" psl 31 1481 | "5 3 2" psl 41 641
## e03 (17,8), mu ~ 55-60: "5 3 2" sl 29 911 | "7 2 3" sl 281 1 | "7 2 3" sl 43 281
## e04 (18,8), mu ~ 51-57: "7 2 4" psl 41 953 | "7 2 4" psl 43 827 | "5 3 3" psl 181 11
## e05 (18,8), mu ~ 62-72: "5 3 3" sl 31 1111 | "5 3 3" psl 41 961 | "7 2 4" psl 43 841
## e06 (19,8), mu ~ 46-49: "5 3 4" psl 41 1361 | "5 3 4" sl 71 131 | "5 3 4" psl 79 191
## e07 (19,8), mu ~ 53-57: "5 3 4" psl 59 461 | "7 2 5" psl 41 1373 | "5 3 4" psl 41 1381
## e08 (19,8), mu ~ 58-71: "5 3 4" sl 41 691 | "5 3 4" psl 61 421 | "7 2 5" sl 41 701
## e09 (20,8), mu ~ 36-41: "7 2 6" sl 29 2689 | "7 2 6" sl 41 953 | "5 4 0" psl 229 11
## e10 (20,8), mu ~ 47-50: "5 4 0" psl 79 271 | "5 4 0" sl 41 971 | "7 2 6" sl 41 967
## e11 (20,8), mu ~ 49-57: "7 2 6" sl 43 841 | "5 4 0" psl 89 191 | "5 4 0" psl 101 131
## e12 (20,8), mu ~ 58-61: "7 2 6" psl 167 29 | "5 4 0" psl 149 41 | "7 2 6" psl 71 379

## e13 Hole anatomy of k = 5 and k = 7 near misses (analysis card, light CPU)
States (copy them into your folder first; never write elsewhere): the director's
/home/user/degree-diameter/research/frontier/raise_d8/runs/d20D8_psl_41_1891_orb5-4-0_s2.sol.best.orb (ORBIT "5 4 0",
psl 41 1891; use the .orb with EVAL for f = 0), and every `*.sol.best` in /home/user/degree-diameter/research/squads/raise_d8b/r2/*/
whose log shows best cost <= 10 (the log tells the group and ORBIT). For each, `EVAL=<copy> UNCPRINT=1` with the same
ORBIT and group lists the holes. Classify each hole: alpha-fixed or not (alpha = conjugation by the printed element,
z -> r z), z = 0 or not, order of the matrix part, in the torus of the alpha element or not. Report a table (state, cost,
#fixed holes, #orbit holes) and say whether fixed points are what stops k = 5 / k = 7 at these mu. Notes in holes.md.

## e14 Small centralizers for k = 7 at (20,8) (screening card)
A fixed element is missed with probability ~ e^(-lambda/k), so for k = 7 the number of alpha-fixed elements (the torus
containing the order-7 element: (p-1)/2 or (p+1)/2 elements in PSL(2,p), times the z fixed by r) matters. Use
`$GRP 20 8 40 60 7 400 3000 P P` for single primes P to find (20,8) groups at mu ~ 45-55 with small tori (p = 13, 29,
41, 43, 83, 97, 113, 127, 139, 167, 181, 197, 211, 223, 239, 251, ...: torus sizes vary) and RANDORB=16 with
ORBIT="7 2 6" on six of them spanning torus sizes; tabulate torus size, mu, min, median, median/7. Then search the best
one for 1400 s.

## e15 Wildcard (D = 8): an approach none of the other cards uses
Other cards: k = 5 and k = 7 orbit Haar searches at all four cells with RANDORB screening, hole anatomy, small
centralizers. Earlier rounds: k = 3 ladders, k = 9 (bad), single orbits of 11 (hopeless), haar_sym product groups
(bad), multi-Haar 2+2 lifts (no better), cyclic/coset Haar graphs (counting bound), near-miss finishing with START.
Find something different that could raise a D = 8 value at d = 17..20, test it at small scale within the box, and
report numbers.

## e16 Wildcard (D = 7): more hubs on the hexagon level graphs
Current D = 7 values (job conics-2, research/synthetic/conics2/README.md): (17,7) 5,693,959, (18,7) 7,309,092,
(19,7) 11,316,940, (20,7) 15,795,219 = (2r+1) copies of H(q) (q = 13, 16) plus K_A + K_B hub vertices; the hub count is
capped by the free slots of the freed sets (README sections 2-4 and the "what was not tried" part). Read the README,
pick one idea that could add hubs (or levels) beyond the caps at these cells, and test it at small q with the
builders in research/synthetic/conics2/ (typed_build.py works for any q with a hex_q*.bin in research/p4/d6/hex/:
q = 3, 5, 7, 9, 11, 13). Report what it would give at (17..20,7), with a small-q all-pairs check
(research/lifts/coordinator_check/apsp.c) of anything you build. No large builds (memory < 1.5 GB).
