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

`wave3/jobs3_<cell>.txt`, made by `wave3/make_all_lists.sh` (screened top groups, 4 seeds each = 301..304, grouped
by seed so every group gets one try before any gets a second). Lower bound = best known N + 1 at the time of writing
(this session's results included). For a second watcher on the same cell, change the seeds:
`awk '{$4 = $4 + 100; print}' wave3/jobs3_<cell>.txt > wave3/jobs3_<cell>_b.txt`.

| cell | list | order window (N) | job length | jobs | suggested watchers |
|---|---|---|---|---|---|
| (6,9) | jobs3_d6D9.txt | 58,753 – 63,000 | 300 s | 64 | 2 |
| (7,8) | jobs3_d7D8.txt | 44,065 – 46,500 | 300 s | 64 | 3 (hardest wall) |
| (8,8) | jobs3_d8D8.txt | 109,621 – 115,000 | 300 s | 64 | 3 |
| (6,10) | jobs3_d6D10.txt | 245,701 – 256,000 | 300 s | 64 | 3 |
| (9,8) | jobs3_d9D8.txt | 241,921 – 252,000 | 300 s | 64 | 3 |
| (7,9) | jobs3_d7D9.txt | 205,321 – 225,000 | 300 s | 64 | 3 (not attacked by haar_gen3 yet) |
| (7,10) | jobs3_d7D10.txt | 1,058,401 – 1,180,000 | 600 s | 64 | 4 |
| (8,9) | jobs3_d8D9.txt | 604,801 – 680,000 | 600 s | 64 | 4 |
| (9,9) | jobs3_d9D9.txt | 1,488,241 – 1,650,000 | 900 s | 64 | 4 |
| (13,8) | jobs3_d13D8.txt | 3,036,961 – 3,500,000 | 1200 s | 48 | 4 |
| (8,10) | jobs3_d8D10.txt | 3,571,777 – 3,900,000 | 1200 s | 48 | 4 |
| (10,9) | jobs3_d10D9.txt | 3,674,809 – 4,000,000 | 1200 s | 48 | 4 |

Where the wall is (this session): the search reaches cost 1–4 and stays there at about 0.80–0.83·N_h
(heuristic.py): (8,8) ~110k, (7,8) ~44.4k, (6,10) ~250k, (9,8) ~244k, (7,10) ~1.06M, (8,9) ~620k, (13,8) ~3.2M.
Near a wall the solve time is heavy-tailed (same group: 0.4 s with one seed, unsolved in 60 s with others), so many
seeds over the best few groups beat long runs; jobs that end with best ≥ 5 point at a weak group.
Huge groups: the time per evaluation is ~5–7 ms at N ≈ 3M (Δ = 8–13), so a 1200 s job does ~200k evaluations.
