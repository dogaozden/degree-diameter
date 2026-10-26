# Card c8 (squad gqd5-r2): exact small-q values for W(q)

Folder: research/squads/gqd5-r2/c8/. Data: build.py writes W5/W7 point-line files; no git commits.

## Settled exactly (q = 5)

1. **Maximum partial ovoid of W(5) = 18.** (Heuristic value was 18, now proved optimal.)
   - Witness of size 18 (found by SAT in 0.1 s), verified pairwise non-collinear in ovoid_sat.py.
   - No partial ovoid of size >= 19 (hence none of size 21), by two independent SAT solvers:
     - `python3 ovoid_sat.py 5 19 cadical195`: UNSAT, 205 s.
     - `python3 ovoid_sat.py 5 19 kissat404`: UNSAT, 97 s (ovoid_K19_kissat.txt).
   - Symmetry used: PSp(4,5) is transitive on ordered pairs of non-collinear points, so WLOG the set contains 0 and a fixed point P1 non-collinear with 0. Sanity check on W(3): max 7 = q^2-q+1, matching the known value.
   - Weaker symmetry (x_0 only) did not finish in 900 s, so it is not a cross-check.

2. **Maximum relaxed set of W(5) = 23.** (Fact 12: T with each point having at most one collinear neighbour in T, and no collinear pair of T on a regular-spread line.)
   - Witness of size 23 (relaxed_bb: 1.2 M nodes, 1.7 s; SA relaxed.c also gives 23 in 60 s, 3 seeds); validated by check_relaxed.py.
   - Upper bound 26 is structural: T has at most one point per spread line (26 lines of the regular spread partition the 156 points).
   - Exhaustive search for size >= 24 is complete. relaxed_bb3 splits the root group 0 into 6 point-branches and one skip-branch. All 7 subtrees returned NONE (about 67-72 s each, about 42 M nodes each). Commands are in section "Commands" below.
   - Method: group B&B with dynamic group ordering (fewest feasible points first) and a skip budget of G - target = 2. Group structure is verified in relax_groups.py: each point off a spread line is collinear with exactly one point of that line.
   - Validation: the same B&B and the SAT encoding (relax_sat.py) agree on W(3) (max 10; K=11 UNSAT both ways).
   - Caveat: the plain SAT encoding did not finish K=24 in 900 s, so the group B&B is the proof method.

## Not settled (q = 5)

3. **Smallest blocking set of W(5): bounds only, 27 <= min <= 30.**
   - Lower bound 27: a blocking set of 26 points must meet each of the 156 lines exactly once, i.e., be an ovoid. W(q) for q odd has no ovoid (Payne-Thas 3.4.1), so |B| >= 27. This is classical, not recomputed here.
   - Upper bound 30: min-conflicts tabu search (block_ls.py) finds a blocking set of 30 points at once.
   - Sizes 28 and 29 not found by local search (best: 6 and 3 unmet lines after 150 k iterations, seeds 2-3).
   - SAT for size 27 (`block_sat.py 5 27 cadical195 sym`) timed out at 600 s, with no answer.
   - Not decided: whether 27, 28, 29 is achievable.
   - So "q^2+2 = 27" is neither confirmed nor refuted here.

## Not attempted in time

- q = 7 for items 1 and 2 (W(7) has 400 points; the heuristics are 33 and the Tallini bound is 43).

## Run times (single-threaded)

- W(5) partial ovoid: K=18 SAT 0.1 s; K=19 cadical 205 s / kissat 97 s; K=20 126 s; K=21 30 s (all UNSAT with P1 symmetry).
- W(5) relaxed: SA 60 s x 3 seeds -> 23; relaxed_bb target 23 1.7 s; target 24 exhaustive: skip-root 67 s, point roots 68-72 s each.
- W(5) blocking set: LS 20 k iterations finds 30 in <1 s; sizes 28/29 do not converge in 150 k iterations; SAT 27 timed out at 600 s.

## Commands

    cd research/squads/gqd5-r2/c8
    python3 build.py 5
    python3 ovoid_sat.py 5 18 ; python3 ovoid_sat.py 5 19 cadical195 ; python3 ovoid_sat.py 5 19 kissat404
    python3 build.py 3 ; python3 relax_groups.py 3 ; python3 relax_groups.py 5
    gcc -O2 -o relaxed_bb3 relaxed_bb3.c
    ./relaxed_bb3 relax_groups_W5.txt 23 | head -1                 # FOUND size 23
    G0="0 1 2 3 4 5"; ./relaxed_bb3 relax_groups_W5.txt 24 -1     # skip root: NONE
    for p in $G0; do ./relaxed_bb3 relax_groups_W5.txt 24 $p; done # point roots: NONE
    python3 check_relaxed.py 5 "$(sed -n 2p bb5_t23.txt)"           # VALID size 23
    python3 relax_sat.py 3 11 ; python3 relaxed_bb3 ...            # W(3) cross-check
    python3 block_ls.py 5 30 1 20000                                # blocking set 30 found
    timeout 600 python3 block_sat.py 5 27 cadical195 sym            # timed out
