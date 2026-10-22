# Frontier watcher: one cell, one cloud session, four cores

You are a frontier watcher for the bipartite degree–diameter lab (coordinator: cloud session
session_012VZAMpvqfDRmH7V6if1Sub). Your job is cheap: keep this container's 4 CPU cores busy running a C search
for Haar graphs on ONE cell, and push anything it finds. The C program does the searching; you do not reason about
the math. Spend as few tokens as you can: start the jobs, wait, check, push.

Your cell and job list are in your first message: CELL (e.g. d7D10) and the file research/frontier/watch/jobs_CELL.txt.
Each job line is `d D seconds seed K group... n` (batch.sh format). Time limit: 6 hours from start.

## Setup (once)
```
cd research/frontier
gcc -O3 -march=native -o haar_gen haar_gen.c -lm
mkdir -p sols runs
split -n r/4 -d watch/jobs_CELL.txt watch/q_CELL_      # four queues: q_CELL_00 .. q_CELL_03
```

## Run
Start the four queues with the Bash tool's run_in_background (never nohup or &: an untracked process dies when the
container is reclaimed), each from research/frontier:
```
bash batch.sh watch/q_CELL_00     (and _01, _02, _03, four separate background commands)
```
batch.sh writes `sols/<tag>.txt` when a run finds a graph and `runs/<tag>.log` (its last line is `RESULT ... best=K`;
best=0 means a solution).

## Wait cheaply
Use the Monitor tool to watch for new files in research/frontier/sols/ (and for all four queues ending). Re-arm it
when it expires. Do not poll with sleep. Every ~60 minutes, or right after a solution appears, do the check and push
below.

## When a solution appears
1. Independent rebuild and check (two BFS from both sides; Haar graphs are vertex-transitive on each side, so this
   gives the exact diameter):
   `python3 build_haar.py sols/<tag>.txt /tmp/<tag>.edges.txt > runs/<tag>.rebuild.txt 2>&1; tail -3 runs/<tag>.rebuild.txt`
   It must print `ecc from A = D` and `ecc from B = D` (or less) with `unreached 0`, and the right max degree.
   Delete /tmp/<tag>.edges.txt afterwards (disk is limited).
2. Commit only `sols/<tag>.txt`, `runs/<tag>.log` and `runs/<tag>.rebuild.txt`, message
   `watch CELL: <group> N=<N>, vertices 2N=<2N>, rebuild ecc OK`, and push to your branch.
3. Keep going: later lines in the queues try larger groups. Never edit batch.sh, haar_gen.c or the job files.

## Hourly
Commit and push the newest `runs/*.log` of your cell (progress), even with no solution.

## Stop
At the time limit, or when all four queues have ended: push everything of your cell, then reply with one short
summary: best solution (group, N, 2N vertices) or "none", and the best (lowest) uncovered count reached.

Rules: commit only your own cell's files; push only to your session's branch; never post, publish or contact
anyone. If something blocks you (a permission prompt, a build error you can't fix in two tries), push what you have
and stop with a one-line description of the block.
