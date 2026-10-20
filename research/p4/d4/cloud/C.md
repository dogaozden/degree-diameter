Task p4-d4 cloud C: weighted 3-ovoids of W(3,q) for q = 9, 11, 13. BRANCH = p4-d4-3.
SETUP (do this first):
1. git fetch origin research-diam4 && git checkout research-diam4   (the code lives there, in research/p4/d4/)
2. Run `scripts/stop_check.sh` before every step; if it prints STOP, push what you have and end.
3. Every long command goes through `scripts/guarded.sh HOURS cmd ...` (HOURS at most 5).
4. pip install ortools numpy  (Python 3.9+). cd research/p4/d4 ; mkdir -p runs sols ; cc -O2 -o runs/hs hs.c ; cc -O2 -o runs/wov wov.c -lm
5. Use all CPU cores you have (check with nproc): run independent jobs in parallel with `&` and `wait`.
6. Every 30 minutes and at the end: copy new results (sols/*.json, runs/*.log, runs/hs_*.out) into
   research/p4/d4/cloud_results/<BRANCH>/ , commit, and push to branch <BRANCH> (git push -u origin <BRANCH>).
   Never push to research-diam4 or master. Never delete anything.
7. Do not write theory or change the scripts' maths. Just run, log, and report numbers. Finish within 5 hours.
Final message: a table of (q, mode, best value, file) and anything that crashed.

Background (do not change): M is a point set of the symplectic quadrangle W(3,q) with at most 1 point on every
totally isotropic line outside a fixed spread S and at most 2 on each spread line. `python3 export_inst.py q st`
writes runs/inst_st_q{q}.txt; `runs/hs INST k0 SECONDS SEED OUT` is a tabu search that prints each larger |M| found and
writes the point list to OUT. `python3 sweep.py q SECS --random N --workers W` runs CP-SAT over random small symmetry
groups and keeps the best M in sols/sweep_st_q{q}.json. A 0/1 vector over points is fine as output.

A weighted 3-ovoid is w: points -> {0,1,2,3} with every totally isotropic line of total weight exactly 3.
Known to exist for q = 3, 5, 7. `python3 cp_w.py q 3 SECS [--sym SPEC] [--workers W] --out sols/w3_qQ_TAG.json`
prints FEASIBLE/OPTIMAL (found) or INFEASIBLE/UNKNOWN.
STEPS:
a. python3 export_inst.py Q po for Q in 9 11 13 (instance with all lines).
b. In parallel (one core each), for Q in 9 11 13 and SEED in 1..(cores/3):
   scripts/guarded.sh 4 runs/wov runs/inst_po_qQ.txt 3 2 14000 SEED runs/wov_qQ_sSEED.out > runs/wov_qQ_sSEED.log
   (prints cost=0 when it finds one and writes the weights; exit code 1 means not found).
c. If cores remain: scripts/guarded.sh 3 python3 cp_w.py 9 3 10000 --workers 4 --out sols/w3_q9_full.json > runs/cpw_q9.log
d. Also try symmetry: for SPEC in t:10 sw fq t:20 fp:1 ns:41 t:16 t:40, python3 cp_w.py 9 3 300 --sym SPEC (q=9);
   for q=11 use t:12 t:24 t:60 sw fq ns:61 ; for q=13 use t:14 t:28 t:84 sw fq ns:85 ns:34 ns:17 . Log all lines.
e. Report for each q: found or not, and the file.
