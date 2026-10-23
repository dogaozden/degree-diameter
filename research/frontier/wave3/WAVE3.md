# Wave 3 recipe: haar_gen3 + screened job lists

Same watcher workflow as watch/WATCHER.md (four queues per container, batch.sh, Monitor on sols/, commit sols + logs +
rebuild), with three changes:

1. Build the new binary:
   ```
   cd research/frontier
   gcc -O3 -march=native -fopenmp -o haar_gen3 haar_gen3.c -lm
   ```
2. Run queues with it (batch.sh is unchanged; BIN selects the binary):
   ```
   BIN=./haar_gen3 bash batch.sh wave3/q_CELL_00      (and _01, _02, _03)
   ```
3. Check with the new checker (all families; same output as build_haar.py plus sha256 and VALID/INVALID):
   ```
   python3 build_haar2.py sols/<tag>.txt /tmp/<tag>.edges.txt > runs/<tag>.rebuild.txt 2>&1; tail -4 runs/<tag>.rebuild.txt
   ```
   (`build_haar.py` cannot read the new families: prime-power fields, prod, agl1, tpgl, csl.)

haar_gen3 is 70–200× faster per evaluation than haar_gen, so a 300–600 s job of haar_gen3 does more search than a
30-minute haar_gen job. Use 300 s for N < 300k, 600 s for N ~ 1M, 900–1800 s for N > 2M.

## Making a job list for a cell

```
python3 wave3/make_jobs3.py d D LO HI SECONDS --seeds 1 --seed0 SEED --screen M --show --fam prod,sl,psl,pgl \
    | python3 wave3/pick_top.py K > wave3/jobs3_CELL.txt
split -n r/4 -d wave3/jobs3_CELL.txt wave3/q_CELL_
```
LO = current best N + 1, HI ≈ 0.9 · N_h (heuristic.py), M = 300 (N < 300k), 100 (N ~ 1M), 20 (N > 2M); K = how many
jobs. Screening costs ~0.2–3 s per candidate group. Use distinct --seed0 per watcher so tags never collide.

`wave3/halving.py JOBFILE --procs 4 --stages 60,300,1200` is an alternative to four batch.sh queues: every group
gets a short run, the best third (lowest final cost) get a longer run with a new seed, and so on.

## Ready-made lists (this session; see HAAR_GEN_NOTES.md for what was already run)

See the `jobs3_*.txt` files in this folder. Each is sorted by order (smallest first) and starts above the best known
order at the time of writing.
