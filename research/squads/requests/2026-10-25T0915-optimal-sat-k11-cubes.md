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
