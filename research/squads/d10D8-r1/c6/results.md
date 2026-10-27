# c6: annealing schedule on the (10,8) proxy, psl 25 73

Proxy: N = 569,400 (PSL(2,25) x Z_73), ORBIT "3 3 1" (k=3, m=3, f=1), mu = 44.81, mu/k = 14.94.
Command template (all runs):

    ORBIT="3 3 1" THREADS=1 [VARS] timeout 900 nice -n 15 research/structured/haar_sym 10 8 120 SEED K OUT psl 25 73

Cap 120 s wall clock. Machine shared (other runs at 86-97% CPU each); our process got 95% CPU in the probe.
"evals" = RESULT evals (candidate evaluations, K per step). For unsolved runs the evals at the cap are shown
(censored). Solve = best=0 and "full diameter check: OK".

## Probe

| variant | seed | secs | solved | evals | best | note |
|---|---|---|---|---|---|---|
| default | 1 | 20 | no | 52,545 | 9 | rate about 2,600 evals/s at full CPU |

## Runs

| variant | seed | solved | evals | best | note |
|---|---|---|---|---|---|---|
| default (TMAX 1.5, TMIN 0.15, COOL 20, REHEAT 150, K 8, TARGP 70) | 1 | no | 265,177 (cap) | 4 | T reaches floor 0.15 at about 66 s; best stays 4 from 90 s |
| default | 2 | no | 174,449 (cap) | 9 | T reaches floor at about 66 s; best stays 9 from 60 s |

Default summary: 0 of 2 solved in 120 s. Median evals at cap = 219,813 (mean of 265,177 and 174,449; the
two caps differ because of CPU share). Median best cost = 6.5.

Observation: with COOL=20 the temperature reaches the floor at about 66 s, and REHEAT=150 never fires
inside a 120 s cap, so the default is one anneal followed by about 54 s of quench at T=0.15 with no progress.

## Variants (queued after the default)


Every run: 120 s cap, nice 15, THREADS=1, ORBIT "3 3 1". Evals = RESULT evals (cap value for unsolved runs).

| variant | seed | solved | evals at cap | best | evals/s |
|---|---|---|---|---|---|
| default | 1 | no | 265,177 | 4 | 2,210 |
| default | 2 | no | 174,449 | 9 | 1,454 |
| COOL=10 REHEAT=60 | 1 | no | 196,945 | 6 | 1,641 |
| COOL=10 REHEAT=60 | 2 | no | 180,937 | 4 | 1,508 |
| TMIN=0.3 | 1 | no | 193,785 | 9 | 1,615 |
| TMIN=0.3 | 2 | no | 250,377 | 6 | 2,086 |
| K=4 | 1 | no | 254,685 | 6 | 2,122 |
| K=4 | 2 | no | 309,837 | 6 | 2,582 |

Median over the 2 seeds:

| variant | median evals at cap | median best |
|---|---|---|
| default (TMAX 1.5, TMIN 0.15, COOL 20, REHEAT 150, K 8) | 219,813 | 6.5 |
| COOL=10 REHEAT=60 | 188,941 | 5.0 |
| TMIN=0.3 | 222,081 | 7.5 |
| K=4 | 282,261 | 6.0 |

Notes:
- No run solved in 120 s. The card's "solves in about a minute" did not hold for seeds 1 and 2 of the default (best 4 and 9 at the cap).
- Default: T reaches the 0.15 floor at about 66 s, and the best is flat from 60-90 s to the end in both seeds. REHEAT=150 never fires inside 120 s.
- COOL=10 REHEAT=60: a reheat fires at about 60 s (T back to 1.19 at 90 s in seed 1); seed 1 stays at best 6 from 30 s to 90 s.
- Evals at cap depend on CPU share (1,450-2,600 evals/s, with other squads' runs on 4 cores). K=4 ran fastest, so its evals count is highest while its best cost is not better. The evals ranking mostly tracks CPU share. The best-cost ranking puts COOL=10 REHEAT=60 first (5.0), but the seed spread (4-9) is wider than the gaps between variants. No variant is shown to beat the default.
- Scoreboard score = 188,941 (median evals at cap of COOL=10 REHEAT=60, censored). valid=false because nothing was solved and checked.
- An earlier queued command hung on stdin and was killed before any solver ran. No results come from it.
