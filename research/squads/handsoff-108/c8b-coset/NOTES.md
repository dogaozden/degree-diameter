# c8b-coset (handsoff-108): notes

Worker: c8b-coset (relaunch of c8-wild idea). Family: bipartite coset graphs over G = PSL(2,181), H = C5 (split torus,
order 5 in PSL), D = union of two regular double cosets H g H (degree 10, |D| = 50). N = |G|/5 = 592,956 per side,
2N = 1,185,912 (> 1,176,480). Seeds 108951-108999.

Files: fastc.c (the code: setup, labels, BFS, validate, bench, anneal, symtest, symscan), fastc_v1.c / fastc_v2.c
(earlier versions, same results), runs/ (logs and best-state files), bench*.out (timings).

## 1. Fast exact cost (done)

- Coset label without a table of group elements. For x = (a b; c d) in SL(2,181), M(x) = (ac, ad, bc, bd) is invariant
  under the torus diag(l,1/l) and determines the torus orbit (up to the 90 PSL classes): 32,942 = q(q+1) classes.
  Inside a class the cosets of H (= the torus elements with dlog = 0 mod 18, i.e. +-mu5) are labelled by
  dlog(ref) mod 18, ref = a if a != 0 else b. So label = 18 * class + (dlog(ref) mod 18), a bijection onto [0, N).
  Checked at setup: every label is hit by exactly 10 SL elements (= 2 * 5), 118,584 regular double cosets (as coset2).
- Representative of a label = torus scaling of the class base matrix (computed, not stored).
- BFS: direction-optimising (top-down while the frontier is small, bottom-up scan of unvisited vertices otherwise),
  visited sets and frontier as bitsets (150 KB). Levels 0..8.
- Validation: all 60 candidates of c8-wild/psl181_h5R2_60.tsv give exactly the same (uncB, uncA) as coset2
  (`fastc validate`; H conjugated to the diagonal torus by the eigenvectors of g0, D conjugated too).
- Speed (machine load 6-7 on 4 cores, so wall times are inflated): coset2 A-root BFS about 0.85 s per candidate
  (CPU time, 20 candidates in 17.5 s). fastc: about 85 ms per BFS, i.e. about 10x. The 20x target was not reached:
  the cost is about 3.5 million neighbour evaluations per BFS (levels 5-7 hold 95 % of the vertices), each about 20 ns.
  Tried: stored representatives (2.4 MB, no gain), per-vertex representative (small gain), bitsets instead of a byte
  array (small gain). Not tried: sorting labels for locality, Barrett-style arithmetic, SIMD.

## 2. Full diameter check: B-B distances (finding)

- coset.c / coset2.c check only the A-root BFS (A-B and A-A distances). B-B distances need a B-root BFS (the group acts
  transitively on each side, so no side swap unless D = D^-1). fastc computes C = uncB_A + uncA_A + uncB_B.
- uncB_B (B-root part) is 0 for 11 of 12 random pairs (1 unit in one): the earlier numbers were nearly full costs.
- If D = D^-1 (the side swap x -> x^-1 style automorphism exists), uncB_B = uncA_A (checked: `fastc symtest`,
  12 of 12 consistent, so the B-root code path is right).

## 3. Anneal (in progress)

Running: `REHEATSTEPS=60 nice -n 10 fastc anneal 3000 108951 15 30 8 psl181_s108951` (COOL=15 s, REHEAT=30 s, K=8 candidates
per step, Metropolis with TMAX 1.5 and TMIN 0.15 in units of 5 vertices, as haar_sym2's schedule; fresh random chain on stall).
Energy = C/5 (units of H-orbits of size 5). Log: runs/psl181_s108951_chains.log (CHAIN lines = descent minima).


### Run 1 (INVALID, bug): psl181_s108951, 22:18-23:08 UTC

- Bug: in anneal() the candidate pair was evaluated as (replaced DC, new DC) instead of (kept DC, new DC), so the
  tracked cost belonged to a different pair than the stored state. Found when recomputing the recorded best pair
  (76843, 880): tracked C 39, true C 166 (`fastc pairparts 76843 880`). The chain minima of run 1 are NOT valid
  and the scoreboard lines of 22:19 and 23:08 are wrong (a correction line is on the scoreboard).
- Fixed in fastc.c (`other = slot ? j : i`); the anneal now ends with a CHECK line that recomputes the current and
  the best pair.
- The symmetric scan (symscan) used cost_pair directly, so its values are not affected (it was stopped after
  a few minutes to free the core for the fixed anneal).

### Run 2 (fixed): psl181_fix_s108952, 2400 s from 23:09 UTC

Command: `REHEATSTEPS=60 nice -n 10 fastc_fix anneal 2400 108952 15 30 8 psl181_fix_s108952`. Results: see below.

### Run 2 result (fixed, 2400 s, 23:09-23:49 UTC): psl181_fix_s108952

- 2198 steps, 17,607 full evaluations, 21 chains (CHECK line: tracked = recomputed for both current and best pair).
- Chain minima (plain vertices, full cost): 45 50 51 52 53 54 55 55 55 60 60 61 64 64 65 69 71 72 75 76
  (last chain unfinished); median about 57 vertices = 11.5 units of 5; best 45 vertices = 9 units.
- Best state: runs/psl181_fix_s108952_best.txt (PAIR line; the two double cosets as SL matrices, DC ids 88243, 66418).
- Haar k = 3 descents (cards): median 6-7 units = 18-21 vertices, best 1 unit = 3 vertices. The coset family is about
  3x worse in vertices, and no better in the best value. The RANDORB minimum over 60 random pairs was 57 (coset.c, A-root
  only); the anneal's best 45 is the full cost of one pair, so the anneal gained only about 20 %.

### Symmetric pairs (D = D^-1, one BFS): random sample of 6,164 pairs (runs/symscan_random2.txt, random order)

- Minimum full cost 431 (about 86 units); the file has one truncated last line (run killed by timeout), ignored. Symmetric pairs are much worse than general pairs (random general pairs
  gave 100-1000 in the bench; the best general pair found is 45). First 163 pairs (runs/symscan_random.txt): min 431 too.
- Self-inverse double cosets: 3,276; pairs of two self-inverse double cosets also give symmetric D (not sampled).

## Summary for the coordinator

- Fast exact cost: validated (60/60 exact vs coset2). Speed about 10x per BFS (not 20x). Full cost needs two BFS
  (A-root and B-root), about 170 ms per general pair under load 6-7.
- B-B distances (B-root BFS) are almost always 0 (11 of 12 random pairs); coset.c's A-root cost is nearly the full cost.
- Anneal over general pairs: best 45 vertices (9 units of 5), median chain minimum about 57 vertices. No cost 0.
- No record. No solution file. Nothing in records/. Processes stopped at the end of the session.
