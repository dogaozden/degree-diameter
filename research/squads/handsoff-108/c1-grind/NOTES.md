# c1-grind (worker c1, squad handsoff-108)

Started 2026-10-31 21:45 UTC. Mandate: about 2 hours of work (to about 23:45 UTC), then leave the two runs alive.

## Runs

Both: ORBIT="3 3 1" RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=3 (F15W3), THREADS=1, nice 15, timeout 25000 s, K=8, d=10, D=8.

| tag | group | N (2N) | seed | haar_sym2 pid | log (CHAIN lines) | out (RESULT) | ckpt |
|---|---|---|---|---|---|---|---|
| g1 | psl 23 97 | 588984 (1177968) | 108101 | 2553 | c1-grind/g1.log | c1-grind/g1.out | c1-grind/g1.ckpt |
| g2 | prod psl 7 sl 8 7 | 592704 (1185408) | 108201 | 3125 | c1-grind/g2.log | c1-grind/g2.out | c1-grind/g2.ckpt |

Launch note: the first launch line was backgrounded as one chain, so g2 failed once (folder not yet there); relaunched by hand with the same arguments.

## Live chain-minimum histogram (this worker, ORBW=3 units; energy is always a multiple of 3)

(refreshed 22:09 UTC by update_live.py)

- g1: chains 30, best 15, median 21, 15:6 18:7 21:11 24:5 30:1
- g2: chains 31, best 12, median 21, 12:1 15:1 18:4 21:12 24:12 27:1


## Pooled reference data (grind branches, read-only via git show)

Source: the 43 unique logs with CHAIN lines on origin/claude/grind-10-8-* (research/d10D8/runs/*.log), restricted to the
ORBW=3 runs (the "ORBW=3: an uncovered" header). Script and data in analysis/ (pool.py, pool2.py, tailfit2.py,
chains_orbw3.tsv, raw/ = the logs).

| group | chains | CPU-h | chains/CPU-h | mean s/chain | min | <=3 | <=6 | <=9 | <=12 | <=15 | median |
|---|---|---|---|---|---|---|---|---|---|---|---|
| psl 23 97 | 5372 | 68.9 | 78 | 46 | 3 | 2 | 11 | 62 | 299 | 1121 | 18 |
| prod psl 7 sl 8 7 | 5479 | 69.7 | 79 | 46 | 6 | 0 | 3 | 36 | 189 | 773 | 21 |

Histogram (energy: count), psl: 3:2 6:9 9:51 12:237 15:822 18:1672 21:1786 24:725 27:68.
prod: 6:3 9:33 12:153 15:584 18:1437 21:2026 24:1110 27:130 30:3.

Tail, lower end (counts for energy 3, 6, 9 = psl 2, 9, 51; prod 0, 3, 33). Ratio n(m+1)/n(m) per 3 energy units:
psl 4.5, 5.7, 4.6; then 3.5, 2.0 (bulk). prod is thinner at the bottom.

Estimate of P(energy 0) per descent (extrapolating the lower tail one or two steps below the lowest seen):
- psl: ratio method 7.6e-5 (1 in 13k); log-linear fits 6.6e-5 to 1.8e-4 (windows 1..3 to 2..5).
  Per CPU-hour: 78 descents, so one energy-0 per about 130-250 CPU-h. The noise is large: the lowest level has only 2 hits.
- prod: 3e-5 to 8e-5 (1 in 13k to 34k), window 1..3 gives 4e-6 but only 3 hits at the next level.
- The card's "P(min <= 9) about 1 in 15" does not match the pooled data: psl gives 62/5372 = 1 in 87, prod 36/5479 = 1 in 152.
  The card's "1 in 15" probably refers to a different bar; flagged here, not changed.

## Scoreboard lines written

- 21:50 UTC: first result, g1 chain min 15 (psl, ORBW=3 units).

## Extra analysis status

- DONE: pooled tail fit (above). Result: P(energy 0) per descent ~ 1e-4 for psl and lower for prod, i.e. one cost-0 per
  ~150-250 CPU-h on psl with this schedule. Consistent with the 14,000 descents so far, none at cost 0.
- Note for c7: the mean chain takes 46 s and the pooled minima need about 46 s x 10^4 = 130 CPU-h per cost-0 hit.

## Log

- 21:45 launched g1 (psl) and g2 (prod), both alive.
- 21:50 first chain minima 15 (g1) and 15 (g2, chain 6). Scoreboard line written.
