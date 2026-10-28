# Card c2: orbit unions under cyclic and 2-generated groups of Sp(4,11)

Files: `orbit_search.py` (the search, run as `P1=240 P2=100 timeout 590 nice -n 10 python3 orbit_search.py`),
`search.log`, `notes_table.tsv` (all 533 groups, one row each, with orbit-size signature and MIP time), `unions.json`
(top 10 distinct unions), `start1-3.txt` (rtabu starts), `rt1-3.txt` (rtabu outputs), `best.txt` (size 89).

## Method

- Random elements from `WSp(11).random_element` (12 random transvections each). An element is kept when its order is
  divisible by 61, 12, 24, 10, 20, 60, 120, 5 or 11 (about 388 of the first 400 sampled elements, 115 of them with 61 | order).
- Cyclic groups: for each kept element g of order o, every subgroup <g^(o/e)> with e | o, e > 1.
- 2-generated groups: <g', h>, g' a power of a kept element, h = f^(ord f / p) for a random element f with p | ord f, p in {2,3,5}.
- Groups with 2 to 150 orbits are solved exactly with `best_union` (MIP, HiGHS): time limit 60 s when there are fewer
  than 100 orbits, 10 s otherwise, and 1 to 15 s for the last groups near the phase deadline (see `exact` column in notes_table.tsv).
  Every returned union was re-checked with `check_relaxed`.
- Groups with a partition already seen are skipped. Group order is the cyclic order, or the closure size for 2-generated groups (">5000" when it exceeds 5000).
- Each MIP runs in a forked child that is killed after time limit + 15 s. Six MIPs (k = 134, subgroup of order 12) hung
  inside HiGHS past its time limit; those groups are listed in `search.log` and not counted.

## Results

Groups processed: 78 cyclic and 449 two-generated (527 total, 6 hung), with 2 to 150 orbits. Best union found: **81**
(cyclic group of order 12 with 126 orbits, 36 pairs, MIP exact). Next: 72 (order 60 two-generated, 30 orbits), 72 (order 12, 122 orbits).

Table (group order, number of orbits, best union; aggregated over groups with the same order and orbit count):

| kind | group order | orbits | groups seen | best union | MIP not proven |
|---|---|---|---|---|---|
| cyc | 12 | 126 | 1 | 81 | 0 |
| 2gen | 60 | 30 | 1 | 72 | 0 |
| cyc | 12 | 122 | 1 | 72 | 0 |
| 2gen | 12 | 122 | 2 | 72 | 0 |
| cyc | 30 | 56 | 7 | 69 | 0 |
| cyc | 15 | 104 | 12 | 69 | 0 |
| cyc | 20 | 82 | 6 | 68 | 0 |
| 2gen | 30 | 52 | 1 | 66 | 0 |
| cyc | 30 | 52 | 1 | 60 | 0 |
| cyc | 20 | 78 | 3 | 60 | 0 |
| cyc | 22 | 74 | 2 | 46 | 0 |
| cyc | 22 | 134 | 5 | 46 | 0 |
| cyc | 11 | 144 | 5 | 46 | 1 |
| 2gen | 40 | 39 | 1 | 40 | 0 |
| cyc | 132 | 24 | 1 | 35 | 0 |
| cyc | 66 | 46 | 1 | 35 | 0 |
| cyc | 44 | 68 | 1 | 35 | 0 |
| cyc | 33 | 86 | 2 | 35 | 0 |
| cyc | 110 | 30 | 4 | 31 | 0 |
| cyc | 55 | 54 | 5 | 31 | 0 |
| 2gen | 1320 | 8 | 12 | 24 | 0 |
| 2gen | 120 | 18 | 2 | 24 | 0 |
| 2gen | >5000 | 3 | 90 | 12 | 0 |
| 2gen | 1440 | 3 | 1 | 12 | 0 |
| 2gen | >5000 | 5 | 53 | 12 | 0 |
| 2gen | 1200 | 5 | 1 | 12 | 0 |
| 2gen | 3960 | 9 | 12 | 12 | 0 |
| 2gen | >5000 | 9 | 5 | 12 | 0 |
| 2gen | 3025 | 12 | 2 | 12 | 0 |
| 2gen | 2640 | 13 | 5 | 12 | 0 |
| cyc | 60 | 30 | 5 | 12 | 0 |
| 2gen | >5000 | 6 | 22 | 2 | 0 |
| 2gen | >5000 | 8 | 4 | 2 | 0 |
| 2gen | 3025 | 10 | 2 | 2 | 0 |
| 2gen | 484 | 13 | 1 | 2 | 0 |
| 2gen | 220 | 15 | 1 | 2 | 0 |
| 2gen | 1210 | 16 | 2 | 2 | 0 |
| 2gen | 100 | 22 | 1 | 2 | 0 |
| 2gen | 242 | 24 | 16 | 2 | 0 |
| 2gen | 110 | 28 | 10 | 2 | 0 |
| cyc | 55 | 32 | 2 | 2 | 0 |
| 2gen | 50 | 40 | 6 | 2 | 0 |
| 2gen | 44 | 43 | 2 | 2 | 0 |
| 2gen | 22 | 84 | 3 | 2 | 0 |
| 2gen | 20 | 86 | 4 | 2 | 0 |
| 2gen | >5000 | 4 | 3 | 1 | 0 |
| 2gen | >5000 | 2 | 65 | 0 | 0 |
| 2gen | 3960 | 4 | 10 | 0 | 0 |
| 2gen | 4840 | 4 | 1 | 0 | 0 |
| 2gen | 3630 | 4 | 2 | 0 | 0 |
| 2gen | 2640 | 5 | 9 | 0 | 0 |
| 2gen | 600 | 6 | 5 | 0 | 0 |
| 2gen | 3300 | 6 | 1 | 0 | 0 |
| 2gen | 726 | 6 | 6 | 0 | 0 |
| 2gen | 1815 | 8 | 1 | 0 | 0 |
| 2gen | 360 | 8 | 12 | 0 | 0 |
| 2gen | 1320 | 9 | 34 | 0 | 0 |
| 2gen | 122 | 12 | 1 | 0 | 0 |
| 2gen | 160 | 13 | 1 | 0 | 0 |
| 2gen | 120 | 15 | 2 | 0 | 0 |
| 2gen | 120 | 20 | 7 | 0 | 0 |
| cyc | 61 | 24 | 13 | 0 | 0 |
| cyc | 60 | 26 | 1 | 0 | 0 |
| 2gen | 24 | 64 | 1 | 0 | 0 |
| 2gen | 24 | 67 | 5 | 0 | 0 |
| 2gen | 24 | 68 | 4 | 0 | 0 |
| 2gen | 20 | 84 | 4 | 0 | 0 |
| 2gen | 18 | 88 | 3 | 0 | 0 |
| 2gen | 12 | 128 | 3 | 0 | 0 |
| 2gen | 12 | 130 | 3 | 0 | 0 |
| 2gen | 12 | 134 | 4 | 0 | 0 |

Full table with orbit-size signatures and timings: `notes_table.tsv`.

## rtabu from the three best unions

Each run: `timeout 900 nice -n 10 research/theorems/d5relax/rtabu research/theorems/d5relax/data/W11_adj.txt 120 SEED OUT -i START`
(120 s instead of the 300 s in the card brief, to stay near the machine budget; the orbit search and the hung-MIP
kills used most of it).

| start | start size | rtabu best | valid (score.py) |
|---|---|---|---|
| start1.txt (cyclic order 12, 126 orbits) | 81 | 89 (found at 4.3 s) | yes |
| start2.txt (2-gen order 60, 30 orbits) | 72 | 89 (found at 0.1 s) | yes |
| start3.txt (cyclic order 12, 122 orbits) | 72 | 89 (found at 2.4 s) | yes |

No run passed 89; target 111 not reached. `best.txt` is the 89-set from start1 (`rt1.txt`), and
`python3 research/theorems/d5relax/score.py 11 research/squads/d5relax-r1/c2/best.txt` prints size 89, valid true.

## Reading

- The best orbit unions (81, 72, 72) come from groups with 30 to 126 orbits; groups with more than 150 orbits were not run.
  Cyclic groups of order 11 to 22 (74 to 144 orbits) give at most 46; cyclic groups of order 15 or 30 (52 to 104 orbits) give 60 to 69;
  the 2-generated group of order 60 (30 orbits) gives 72; cyclic groups of order 60 give at most 12.
- rtabu from these starts reaches 89 in every run, the same value the free search reaches in under a second, so the orbit
  starts add no new structure and no run went past 89.
