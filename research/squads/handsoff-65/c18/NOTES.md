# c18 notes (card: Haar graphs with hub orbits, types "1,k|1,k", mcos)

## Model (checked by hand)
Type "1,k|1,k": A = A0 (regular, |G|) + A1 (hub orbit G/H, |H| = k); B = B0 (regular) + B1 (hub).
Blocks n_ab (double cosets per block, from mcos's degree rule): n00 + n01 = 6 (A0), 6(n10+n11) = 6 (A1),
n00 + n10 = 6 (B0), n01 + n11 = 1 (B1) for k = 6. Solutions: n11 = 1 (disconnected: A0+B0 and A1+B1 split) or
n11 = 0, n00 = 5, n01 = n10 = 1 (the connected one). So N="5,1,1,0" (row-major: (A0,B0),(A0,B1),(A1,B0),(A1,B1)).
n = 2|G| + 2|G|/k = 7|G|/3 for k = 6; needs 6 | |G| and an element of order 6 (cyclic stabiliser for mcos).
Other k: "1,3|1,3" n = 8|G|/3 (|G| >= 258, 3 | |G|), "1,2|1,2" n = 3|G| (|G| >= 230), "1,4|1,4" n = 5|G|/2 (|G| >= 276).

## Tools
- Group tables: GAP from shared/gap_tables.g into c18/groups (orders 294, 300, 306, 312 generated; c5 has only 342-380).
- c18/has6.py TABLE...: counts element orders (which groups have order-6 elements).
- c18/screen.sh TYPE N SECS SEED DEADLINE TABLE...: mcos on each group, appends scan/<TAG>.tsv (group, name, type, N, best, sec).
- Calibration: TYPE "1|1" on SmallGroup(342,12), SEED 4, 22 s -> cost 0 (684 Haar graph, check.sh VALID). SEED 2 and 3 stalled at 4 in 30 s.
- Note: the bash tool has a 120 s limit by default; pass timeout 300000 explicitly or the job gets backgrounded.

## Results
- 1,6|1,6 N=5,1,1,0: 300_13 (ord6 = 50) 3 s -> cost 53 (n 700). Screen at 8 s per combo, see scan/1-6_1-6-5-1-1-0.tsv.

## t18: tabu search for "1,k|1,k" (new, 19:20+)
Source: c18/t18.c (gcc -O3 -march=native -o t18 t18.c -lm). Full-neighbourhood tabu: every step evaluates all single
moves (one element of S/G01/G10/G11 changed to any group element, or H/K changed to another cyclic subgroup of order k),
takes the best non-tabu move (aspiration on new best), perturbs 2 slots after 400 steps without improvement.
Cost = number of (representative, vertex) pairs at distance > 5 over the 4 orbit representatives (same scale as mcos).
Blocks: S = A0-B0 elements (x ~ x s), G01 = A0-B1 elements (x ~ coset of x g in G/K), G10 = A1-B0 elements (coset xH ~ x h g),
G11 = A1-B1 elements (coset xH ~ coset of x h g). N=5,1,1,0 is the k=6 type.
Command (exact):
  TLIM=200 ./t18 groups/sg_294_11.txt 6 5,1,1,0 SEED ITERS TENURE OUTFILE HGEN KGEN
  e.g. TLIM=200 ./t18 groups/sg_294_11.txt 6 5,1,1,0 8 100000 12 t294_11.edges 14 5    (reproduces cost 2 at step 738, ~144 s)
Outputs: OUTFILE (edge list, rewritten at every new best) and OUTFILE.par (S, G01, G10, G11 values, H and K generators, cost).
Restart from a saved state: INIT=cost2_294_11.init TLIM=200 ./t18 groups/sg_294_11.txt 6 5,1,1,0 SEED 100000 12 OUT
(INIT file: 4 lines of block values, then "H g K h"; the .init file here is the cost-2 state).
Cost-2 state (SmallGroup(294,11), H = <155>, K = <80>): S = {69,212,139,165,129}, G01 = {245}, G10 = {91}, G11 = {}.
Edge list cost2_294_11.edges: n = 686, 2058 edges, simple, bipartite, degree 6, bad = 294 far pairs (check.sh). Verified.
Results: seed 8 cost 2 (200 s); seed 21 cost 5; seed 9 with tenure 25 cost 7; the mcos annealer with the same group
stayed at 5 for 200 s. So t18 tabu beats mcos SA on this family.

## Status 20:03 UTC (t18 results, all k=6, N=5,1,1,0, random or fixed H/K)
- Second cost-2 state (seed 88, random H/K, 131 s): cost2b_294_11.init (S={16,220,4,56,15}, G01={259}, G10={256},
  H=<158>, K=<118>), edge list s88_294_11.edges; reproduce with
  `TLIM=170 ./t18 groups/sg_294_11.txt 6 5,1,1,0 88 100000 12 OUT` (writes OUT and OUT.par; OUT is cost 2 at step 731).
  Edge list verified below in NOTES (check.sh).
- Restarts from the cost-2 states (INIT=..., seeds 31, 77 with tenure 20, 123): stay at 2 for 150-200 s, never reach 1.
- Fresh seeds on 294_11: seed 8 -> 2 (144 s), seed 40 -> 5, seed 9 (tenure 25) -> 7, seed 21 -> 5, seed 99 -> 5 (150 s), seed 88 -> 2.
- Screen of all order-294 groups with elements of order 6 (t18, 55 s, seed 3, random H/K), best cost:
  294_11 2 (deep), 294_12 8 (170 s deep: 4), 294_8 10, 294_9 14, 294_17 16, 294_1 20, 294_14 22, 294_10 23,
  294_13 23, 294_2 30, 294_15 27, 294_16 26, 294_18 54, 294_19 158, 294_4 176. (294_0 abelian excluded.)
- Scoreboard: c18 line for n=686, bad=294 (cost 2) written at 18:5x (t294_11.edges, verified by check.sh).
- mcos (shared/mcos, SA) on the same family: 294_11 cost 5 at 200 s, so t18 tabu is the better tool here.
- Calibration: mcos 1|1 on SmallGroup(342,12) reaches cost 0 (684 Haar graph, VALID) with SEED 4 in 22 s.
- Order 3/2 types ("1,3|1,3" N=4,2,2,0; screened 258/264/270 with mcos 5 s/combo, best SmallGroup(258,2) cost 11 at
  n=688) were left alone as the coordinator asked (other workers take 1,3 and 1,2).
- Infeasible in the mcos/full-double-coset model: "1,4|1,4" (4 does not divide 6).

## Next (if continued)
- More tabu seeds on 294_11 and 294_12 from the two cost-2 states with bigger perturbations (stall limit 400 is in t18.c).
- Cost-2 solutions have far pairs between same-side vertices (viol.py shows 2 far vertices per A0 representative):
  a targeted move set that adds a 4-cycle-breaking swap might help; not tried.
- No bad=0 found; nothing above 684 with cost 0.
- s88 edge list re-checked at 20:03: n 686, bad=294 (cost 2), simple, bipartite, deg 6.
- 20:05 INIT restart (seed 200, tenure 30) and 20:08 fresh seed 300 (tenure 15, 200 s, cost 5): no cost 1 found.
- Final state 20:09: best = cost 2 (bad 294) at n=686, SmallGroup(294,11); no processes of mine running.
