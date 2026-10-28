# c13: random baselines (calibration)

Runs: run_calib.py -> results.jsonl (96 records: 3 Delta x 2 groups x 2 kinds x 8 seeds, primes 23..113).
Table: analyze.py -> table.txt. Each family_score call is `--qrange 23 113`, m = 1.

Families
- sym: gen_random_orb.py {q} f 2 SEED (haar_families). f = Delta - 6 fixed letters from {I, w}: Delta=6 has none,
  Delta=7 has {I}, Delta=8 has {I, w}; plus 2 random alpha-orbits of size 3. I IS included for Delta 7 and 8.
- nosym: c13/gen_random_nosym.py {q} Delta SEED. Delta distinct random elements of SL(2,q), no alpha-closure.
  I is NOT included (excluded and treated as the identity class). Distinct in PSL (X and -X count as one).
  Seeded by SEED*1000003 + q*101 + Delta.

Per-cell statistics (8 seeds)
- mean and SD of mean_excess over seeds; per-q SD = for each q, SD over the 8 seeds of excess(q), averaged over q.

See table.txt for the full table (min and max of mean_excess included).

Observations
- Seed-to-seed SD of the 22-prime mean is about 0.02-0.11; the spread is small against the gap to records (2.0-2.3).
- Random nosym S beats symmetric S for Delta 7 and 8 (psl 2.95 vs 3.04, 2.95 vs 3.28) and for sl Delta 6-8.
- Diameters are concentrated: different random S give nearly the same integer diameter per q (the excess differs
  mainly through the integer), so per-q SD is driven by integer jumps.
- The sym psl Delta=6 mean of 3.31 is consistent with the ~3.2-3.5 quoted in the preamble.
- The first pass was cut at 55 records by a 900 s timeout wrapper; run_calib.py was resumed (done-set skip).
