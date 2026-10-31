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
