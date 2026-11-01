# h4 notes (deep-65 round 1): tabu over (S, K, H, R) for the hub families k = 2 and k = 4

Start 02:38 UTC, last run 03:01 UTC. All runs single-threaded, each shell command under 110 s.

## Files
- hubk.c: copy of tools/hubk.c (cost = all_conditions, exact search "ex" unchanged).
- hubtabu.c: hubk.c with its main renamed main_hubk (rand and ex modes unchanged) plus the tabu search
  (mode "tabu", appended after the old code). Build: gcc -O3 -march=native -o hubtabu hubtabu.c -lm
- groups/: GAP tables (tools/gap_tables.g) for orders 230, 232, 234, 276, 280 (sg_ORDER_i.txt, .name).
- score65.c, apsp.c: copies of shared/score65.c and shared/apsp.c (built here). apsp not run: no cost-0 state.
- runs/: screen_k2.log, screen_k4.log (short screens), deep_*.log (deep runs), edges_*.txt (edge lists).

## Validation
- `hubk groups/sg_230_3.txt 2 rand 50 1` (and sg_234_1, sg_232_6 with k=2; sg_276_9, sg_280_5 with k=4):
  0 mismatches between the six predicted misses and BFS (3 groups k=2, 2 groups k=4, 40-50 trials each).
- hubtabu rand mode identical (same code): 0 mismatches on sg_230_3 k=2 and sg_280_5 k=4.
- Cost-0 policy: all_conditions total 0 is the diameter-5 test. Cost 0 never reached; no graph was scored as a record.
- Check of the cost unit: the cost-3 graph of SmallGroup(280,35) (k=4, n=700) scores bad = 560 with score65.
  One missing element of the group in a Haar-type condition is ~280 bad pairs, so cost counts orbits of pairs.
  The cost-7 graph of SmallGroup(234,1) (k=2, n=702) scores bad = 1053.

## Search (hubtabu.c, tabu_run)
- State: S (5 distinct elements), K and H (subgroup indices, order k), R (union of H-K double cosets of total size
  k(6-k) = 8 for both k = 2 and k = 4; chosen by index list selR).
- Full neighbourhood each iteration: S-element to any group element (5 m moves); K (resp. H) to any other subgroup
  of order k with R re-sampled (best of 3 random valid R); R double coset to an unused one of the same size.
- Tabu: old S element, old K/H index and removed double coset (by least element) for TENURE iterations; aspiration.
- Stall: STALL iterations without segment improvement -> perturb 1-3 S elements (and maybe R); after 20 perturbations,
  restart at random. Speed about 10 ms per iteration for m = 230-280.

## Commands and results
Screens (one seed, 5-7 s each, all nonabelian groups): `hubtabu groups/sg_O_i.txt k tabu 7 1 - 300` (k=2, O=230,232,234)
and `... 4 tabu 5-6 1 - 300` (k=4, O=276,280). Full list in runs/screen_k2.log and runs/screen_k4.log.
Deep runs (best cost per group):
- k=2, n=690 (230): SmallGroup(230,1) cost 10 (seed 2, 28 s; seed 3, 40 s: 14). SmallGroup(230,2) screen 20;
  SmallGroup(230,3) (D230, 115 involutions) 236.
- k=2, n=696 (232): SmallGroup(232,10) cost 20 (seed 2, 25 s); 232_3 47, 232_12 42 (screen only).
- k=2, n=702 (234): SmallGroup(234,1) cost 7 (seed 2, 28 s; seed 3, 42 s: 7 with miss 1,1,0,4,1,0; seed 4, 40 s: 7);
  234_3 12 (28 s), 234_7 13 (20 s), 234_14 18, 234_4 17, 234_2 17, 234_12 17 (screen).
- k=4, n=690 (276): SmallGroup(276,1) cost 68 (seed 2, 30 s); 276_8 69 (30 s).
- k=4, n=700 (280): SmallGroup(280,35) = C2 x (C5:(C7:C4)) cost 3 in 7 of 8 runs (seeds 2-8, 15-80 s, stall 80-600,
  tenure 3-15). Miss patterns seen: 0,1,0,2,0,0 and 2,0,0,0,1,0. SmallGroup(280,34) cost 9 (25 s, two seeds);
  280_32 cost 25 (18 s); 280_33 34 (screen).

## Observations
- Groups with many involutions (dihedral-like, e.g. D230, D232, D234, C2xC2xD58) are far worse for k=2 (cost 236-250
  at 7 s); groups with few involutions (C23xD10, C13:C18) are best.
- For k=4 the screen is dominated by the subgroup count: 280_35 has 75 subgroups of order 4 and reaches cost 3 in
  seconds; the cost 3 floor was reached repeatedly from different seeds, so it looks like a family limit for this group,
  not a search failure. Not checked: exact search on 280_35 (too large per the card).
- No cost-0 state was found in any (k, order) pair. No apsp run.
