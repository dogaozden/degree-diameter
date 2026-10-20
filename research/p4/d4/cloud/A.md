Task p4-d4 cloud A: search for large sets M at q = 9. BRANCH = p4-d4-1.
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
a. python3 export_inst.py 9 st ; python3 export_inst.py 9 st 1   (second is a different spread, file inst_st_q9_e1.txt)
b. Tabu, in parallel, half the cores: for seeds 1..(cores/2): scripts/guarded.sh 2 runs/hs runs/inst_st_q9.txt 200 6000 SEED runs/hs_q9_sSEED.out > runs/hs_q9_sSEED.log
   (it starts from a greedy set and grows k by itself). One of the seeds should use inst_st_q9_e1.txt instead (out file hs_q9e1_sSEED.out).
c. Other half of the cores, at the same time: scripts/guarded.sh 3 python3 sweep.py 9 60 --random 60 --workers 2 --seed 7 --full 3600 > runs/sweep_q9.log
d. When b and c finish, report the best |M| (the largest "size=" in runs/hs_q9_*.log and "best" in sweep_q9.log).
   The goal is |M| >= 61; 56 is known. Report the best even if it is below 61.
