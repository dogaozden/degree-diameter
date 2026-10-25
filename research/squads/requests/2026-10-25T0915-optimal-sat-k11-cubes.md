# Compute request: optimal-sat, (11,3,−2) cube-and-conquer (certified)

From: optimal-sat lead session (branch `claude/optimal-sat-nx83w2`, draft PR #322). Not a squad: plain CPU jobs.

## Why
If the instance below is UNSAT there is no bipartite (11,3,−2)-graph, so **N^b(11,3) ≤ 218** (wiki: 220). The
reduction is Theorem Q in `research/projects/optimal-sat/SUMMARY.md`. k = 5..10 are done and DRAT-verified. The k = 11
instance has run for about 3 CPU-hours on each of 3 solvers in the lead's 4-core container without an answer.

## Jobs (independent; one core each)
Setup on each machine: `pip install python-sat`; build CaDiCaL (github.com/arminbiere/cadical:
`./configure && make`) and lrat-check (github.com/marijnheule/drat-trim: `gcc -O2 -o lrat-check lrat-check.c`).

    cd research/projects/optimal-sat/defect2
    python3 cube_list.py 11 2 cubes11_r2.json --sym --nf2 --ntt --alltr      # 110 cubes (deterministic)
    CADICAL=... LRATCHECK=... ./run_cube.sh cubes11_r2.json <i> out/        # i = 0..109

Each job prints one line, e.g.
`cube 17 sha256 ... cadical_rc 20 's UNSATISFIABLE' lratcheck_rc 0 VERIFIED wall ... s`. The proof is streamed into
lrat-check through a named pipe, so nothing large is stored. Per-cube cost is unknown; it is at least 30 CPU-minutes
(two sample cubes are still running). A finer split is `cube_list.py 11 3 ...` (2535 cubes).

Then, once: `DRATTRIM=... python3 cover_check.py cubes11_r2.json work/` (checks the cubes are exhaustive; seconds).

**If any cube prints SATISFIABLE**, keep the model: it is an oriented graph A, which may or may not have the signing.
Check it with `signs_gf2.py` (needs the model decoded; see `cegar.py`), and tell the lead. A signable A would be a
220-vertex (11,3) graph, which is optimal.

## Report
Append the 110 lines to `research/projects/optimal-sat/logs/k11_cubes.log` on a branch, or send them to the lead.

## Update 11:40 UTC: a better split (degree-sequence cubes)

`defect2/ablist.py` lists 245,667 cubes (α, β) = sorted row and column sums of the 9×9 block B (arcs O→I at
vertex 0). The pruning rules are proved in NOTES.md. `defect2/abcube.py` builds a cube from a shared base CNF
(`abcube.py base 11 base.cnf`) in under a second. `defect2/run_abcube.sh base.cnf '<cube>' out/` solves it with a
streamed LRAT check. A random sample of 20 cubes (kissat, loaded 4-core machine):
- 16 took about 1 s;
- the others took 3 s, 19 s and 262 s, and one was > 300 s.

Hard cubes are those with small t and flat α. Rough total: 10³–10⁴ CPU-hours. The cubes are exhaustive by a
relabelling argument (sort the degrees; block-transposition lex-leader inside each cube), not by a drat-trim cover
check. Whichever of the two splits is used, a SAT cube means: decode A and run `signs_gf2.py`.

## Update 12:45 UTC: turnkey workers

    cd research/projects/optimal-sat/defect2
    bash setup_worker.sh ~/w                 # builds CaDiCaL + lrat-check, base CNF, cube list (245,667 cubes)
    bash worker.sh ~/w <i> <n> 4             # worker i of n, 4 cubes in parallel; log in ~/w/out/abcubes.log

Each cube runs with a certified LRAT check and a 1-hour limit (CUBE_TIMEOUT). Cubes with t ≤ 3 add the valid
"vertex 0 has the most directed triangles" constraint; with it t = 0 is solved in 55 s instead of more than 15 min.
Send back the abcubes.log lines (or push them to a branch). Unsolved cubes go into a second pass, either with more
time or with a finer split.

## Update 14:00 UTC: recommended recipe (rule R1)

Use rule R1, "vertex 0 lies on the most directed triangles", with the reversal-halved list `ablist.py` (245,667 cubes).
`run_abcube.sh` adds the R1 constraint for t ≤ MAXT_BELOW (default 3) and solves without it otherwise. That is
consistent: a cube may omit its rule's constraint, but the whole split must use one rule. The 8 cubes with t ≤ 3 are
being certified in the lead's session (see `logs/k11_lowt.log`). Measured costs and the alternative rule R2 are in
`research/projects/optimal-sat/logs/defect2_calibration.md`.

Expected: most cubes take seconds; a minority of low-t, flat-α cubes take minutes to hours. Do a first pass with
CUBE_TIMEOUT=600, then a second pass on the leftovers with more time. If leftovers stay hard, split them by rows of B
the same way `cube_list.py` does.
