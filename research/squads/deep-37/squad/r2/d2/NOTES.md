# Card d2 (deep-37 round 2): exact G-invariant search at n = 169, (Delta, D) = (3, 7)

Target: bipartite, max degree 3, diameter 7 on 169 vertices. Sides A = 85 (colour 0), B = 84 (colour 1); def(A) = def(B) + 3.
Case run here: B cubic, exactly three degree-2 vertices in A, forming one G-invariant set (a union of orbits of total size 3).
Same-side distance <= 6 is the only real condition (cross pairs follow, all degrees >= 1).

## Code
- `orbdfs169.c` / `orbdfs169` (built with `gcc -O2`): orbdfs extended to per-vertex target degrees.
  - env `DEG2` = file of vertex ids or comma list; these get target 2, all others 3. Checked: the set is G-invariant,
    and the target sums agree on both sides (edge count).
  - Orbit types include the target, so interchangeable untouched orbits have equal targets.
  - Prune for non-cubic targets: for each discovered orbit representative r, dist = distinct endpoints of NB walks of even
    length <= 6 from r; poss = sum over partial walks P ending at v (length l <= 5) of f(v) * TB[l], f(v) = target - degree,
    TB[l] = sum of 2^k over k in [0, 5-l] with l+1+k even. Prune if dist + poss < size of r's colour class.
    For all targets 3 this is the old cubic prune (same node counts, see validation).
  - Test switch `NOPRUNE=1` (used only for the soundness check below).
- `gsets169.g` (GAP, smallgrp): enumerates G-sets: multisets of admissible subgroup classes (stabilisers {2,3}-groups) for A
  (degree-2 part with index sum 3, degree-3 part with index sum 82), and for B (index sum 84). Colour-preserving only,
  faithful actions only. Files ordered by total orbit count; writes `TAG_i.txt` (group file) and `TAG_i.deg2`.
- `run169.py DIR TL BUDGET`: runs orbdfs169 (D = 7) on the G-sets of a directory, logs to `runs.tsv`; checks any solution
  with bin/score37.
- `longrun.py TL FILES...`: same with a longer timeout (used for the timed-out order-12 sets).

## Validation
- Cubic calibration, n = 168 (`inputs/r2f_grp168_f21.txt`, all targets 3): bin/orbdfs and orbdfs169 both give
  DONE nodes=619184 sols=96; the solution edge sets agree (token-level comparison of all 96 solutions).
- `runs/f20rev/f20rev_b1.txt` (n = 170, F20 colour-reversing G-set): both DONE nodes=403559 sols=0.
- Non-cubic soundness: 12 vertices (6+6), degree-2 vertices 4,5,10,11 (one per side pair), trivial group and two C2 actions
  (one fixing the degree-2 vertices, one swapping them), D = 3 and D = 5. For every case, the pruned leaves equal exactly the
  no-prune leaves that satisfy the same-side condition (checked independently in Python, `soundcheck.py` in scratchpad).
  Examples: trivial group D = 5: 1741 unpruned leaves, 1594 valid, pruned run returns the same 1594.
- Caveat: no independent brute-force check was done for the 169 case itself; the 0-solution results rest on the prune
  soundness tests above and the cubic validation.

## Runs (exact search, timeout 8 s per G-set in the bulk pass)
Enumeration caps (not complete for every group): max orbits per side MP and max G-sets per group:
order 12: MP 9, 3000 (groups 1-3 complete for MP 9, groups 4-5 capped); order 18: MP 8, 528 (groups 1-2 complete), 3000 (3-5);
order 24: MP 6, complete for groups 1-5 (7790/7035 files), 3000 cap for 6-15 (some may have more); order 36: MP 5, 1500 cap
(group 9: 696 complete); order 48: MP 4, 800 cap per group (52 groups, all run).
Total G-sets processed: about 108,400 settled (DONE 107,709 + EXCL 688) at the time of writing.
- DONE with solutions: 0. No far-0 graph at n = 169 among these G-sets.
- EXCL (EXCLUDED_TWIN): 688, a non-identity element fixes all of one side, twin bound 65 < 84.
- Node counts of the DONE runs: 80,498 with 1 node (root killed at once: e.g. a G-fixed vertex with target 2 or 3 has no
  admissible G-invariant neighbourhood), 24,627 with 2-10 nodes, 2,584 with more than 10 nodes (max 381,434).
- TIMEOUT at 8 s: 75 sets, all in order-12 groups (g12_1 to g12_5). longrun.py (60 s each) was started on them at 01:01Z;
  see the end of this file for its result.
- ERR: 1 (a truncated stale file, g24_5/s_7036, from an interrupted earlier run; not a G-set result).

## Not done
- Order-12 G-sets beyond the first few hundred (g12_4, g12_5 each have 3000 files; most not run yet, and the tree sizes are large).
- Order 6, 4, 8, 9, 16 and other small groups: not generated (all have >= 7 orbits per side or more; groups of order 2^a are
  not covered by the card's list).
- Multisets are not reduced modulo Aut(G), so isomorphic G-sets can appear more than once.
- Groups of order 60 or larger, and the case with def(B) > 0.
