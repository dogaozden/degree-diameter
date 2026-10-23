# Wave-3 frontier watcher: one cell slice, one cloud session, four cores, haar_gen3

Same job as WATCHER.md, with the faster program (haar_gen3) and the checker that reads every group family (build_haar2.py).
Spend as few tokens as you can: start the jobs, wait, check, push. Never edit the C code, batch.sh or the job files.
Your CELL id (e.g. d8D9w2) and job list research/frontier/wave3/jobs3_CELL.txt are in your first message. Limit: 6 hours.

## Setup (once), from research/frontier
```
gcc -O3 -march=native -fopenmp -o haar_gen3 haar_gen3.c -lm
mkdir -p sols runs
split -n r/4 -d wave3/jobs3_CELL.txt wave3/q_CELL_
```
## Run
Four separate Bash calls with run_in_background (never nohup or &): `BIN=./haar_gen3 bash batch.sh wave3/q_CELL_00` (and _01, _02, _03).
## Wait
Monitor tool on research/frontier/sols/ (re-arm when it expires). No sleep polling, no send_later or other scheduling tools.
## When a solution appears
`python3 build_haar2.py sols/<tag>.txt > runs/<tag>.rebuild.txt 2>&1; tail -5 runs/<tag>.rebuild.txt` — it must end with VALID.
Commit only sols/<tag>.txt, runs/<tag>.log, runs/<tag>.rebuild.txt and push to your branch. Keep going.
## Hourly
Commit and push your newest runs/*.log. At the limit or when the four queues end: push everything and reply in one line:
best solution (group, N, vertices) or "none".
Rules: push only to your branch; never post or contact anyone. If blocked (a prompt, a build error after two tries), push and stop with one line.
