Task p4-d4 cloud B: search for large sets M at q = 11 and q = 13. BRANCH = p4-d4-2.
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

STEPS:
a. python3 export_inst.py 11 st ; python3 export_inst.py 13 st
b. Tabu in parallel, using all cores, split between q=11 and q=13:
   scripts/guarded.sh 4 runs/hs runs/inst_st_q11.txt 85 12000 SEED runs/hs_q11_sSEED.out > runs/hs_q11_sSEED.log
   scripts/guarded.sh 4 runs/hs runs/inst_st_q13.txt 120 12000 SEED runs/hs_q13_sSEED.out > runs/hs_q13_sSEED.log
   (different SEED per job).
c. After b, if time remains: scripts/guarded.sh 1 python3 sweep.py 11 60 --random 30 --workers 2 > runs/sweep_q11.log
d. Report the best |M| for each q ("size=" lines). Goals: q=11: >= 97; q=13: >= 141. Report the best even if lower.
