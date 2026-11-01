# c1b-structure (worker c1b, squad handsoff-108)

Question (card): is there a cheap statistic of an orbit set S (psl 23 97, ORBIT="3 3 1", F15W3 energy) that separates
descent ends from random sets, and does a biased start (best of 50 random sets by that statistic) end lower?

Started 2026-10-31 23:45 UTC. Mandate about 2 hours (to about 01:45 UTC).

## Tools (this folder)

- `haar_c1b.c`: copy of research/d10D8/sym2/haar_sym2.c (same CLI, same cost, same RESULT/CHAIN format) plus:
  - `STATS=rand STATS_N=m`: m random symmetric sets; `STATS=file STATS_FILE=f`: sets listed as `tag s0..s9`.
    Output per set: tag, energy (ORBW=3), plain uncovered, uncovered fixed elements, ball sizes lev1..lev7, element
    orders of the 10 letters, then the set. One BFS per set (about 0.4 ms of CPU).
  - `BIASN=n BSTAT=...`: at every fresh chain start with an even chain index, take the best of n random sets by BSTAT
    (lower is better). BSTAT=C3E: collisions at distance 3 first (820 - ball(3)), then energy.
  - CHAIN lines now also print `arm R|B startE startstat` (startstat = 1000*c3 + energy for C3E).
- `extract_ends.py`: chain-end sets (CHAIN S lines, ORBW=3 logs of the grind runs) -> `chainends_{psl,prod}.txt`.
- `good_{psl,prod}.txt`: the 119 states of shared/good_states.tsv per group.
- `analyze1.py`, `analyze2.py`: statistics table and the distance-3 collision analysis. `analyze_ab.py`: A/B summary.
- `run_ab.sh`: the interleaved A/B run (one process).

Checks: the tool reproduces every recorded energy of the 80 psl good states (0 mismatches; energies 3, 6, 9).
Ball sizes: |B(distance 1)| = 10, |B(2)| = 91 (tree), |B(3)| = 820 (tree bound 1 + 10 * 9 * 9 = 820 on the B side).

## Statistics: good sets vs random sets (psl 23 97; 20,000 random sets; 80 good; 796 chain ends)

Random energy: min 27, p1 57, median 141 (plain uncovered: min 27, p1 54, median 141). Good: energy 3, 6, 9.
Chain ends (energy 6..30): median 18. (prod: random median 129, chain ends median 21, 863 ends, 39 good.)

Collisions at distance 3, c3 = 820 - ball(3) (AUC = P(good > random), 0.5 = no separation):
| set | c3 = 0 fraction | median energy (among those) |
|---|---|---|
| random psl (20,000) | 0.085 (1,691) | c3=0: 90; c3=3: 108; c3=6: 126 |
| good psl (80) | 0.89 (71) | 9 |
| chain ends psl (796) | 0.84 (666) | 6..30 |
| random prod (20,000) | 0.30 (6,064) | c3=0: 99 |
| good prod (39) | 1.00 | 9 |
| chain ends prod (863) | 0.95 (821) | 6..30 |

AUC good vs random: c3 (ball 3) 0.94 psl, 0.85 prod; ball 4 0.98 / 0.96; ball 5 0.99 / ...; ball 6 0.998. Fixed-element
misses 0.30 (psl). Element-order counts (involutions, orders 3/4/6): the typical set has none of them (median 0 of
the 9 non-e letters; median 9 have order > 6), and AUC is 0.50 for every order count, so no signal there.
Interpretation so far: the statistic that separates is "no relation of length <= 3" (c3 = 0). Among random sets it is
strongly tied to energy (correlation -0.63 with ball 3 and -0.9 with ball 6), and the annealer ends with c3 = 0 in
84 to 95 % of chains. So it is a property the descents already reach, not evidence that the start decides the end.
Next: the A/B test (below) decides whether a c3 = 0 start changes the chain minima.

## A/B run (interleaved, one process)

- Command: run_ab.sh = ORBIT="3 3 1" ORBW=3 RESTARTAFTER=0 COOL=15 REHEAT=30 VCLOCK=0.003333 BIASN=50 BSTAT=C3E,
  seed 108151, K=8, psl 23 97, nice 10, timeout 5400 s. Chain 1 and every odd chain: random start (R); every even
  chain: biased start (B). Step-based schedule (VCLOCK = 1/300 s per step), so both arms see the same schedule.
- Log: ab.log (CHAIN lines). Summary: `python3 analyze_ab.py` (in this folder).
- Speed under load (load 7 on 4 cores): about 8 ms per step, so a chain of about 14,000 steps takes about 2 minutes.
  Expect about 25 chains per arm in the window, not the 60 the card asks for; reported as such.

