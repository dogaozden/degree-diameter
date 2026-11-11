# c3c-grind (worker c3c, squad handsoff-108)

Card: one more fresh-seed F15W3 grind on psl 23 97, until 03:25 UTC (relaunch of slot c3, 01:40 UTC).
Seeds 108471-108480 (restart = next seed). Start 01:37 UTC, end 03:24:28 UTC (run ended by its own budget, no kill needed).

## Run

- Command (c1-grind g1 command, card seed and nice): `ORBIT="3 3 1" RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=3 CKPT=g3.ckpt THREADS=1
  nohup nice -n 12 timeout 6469 .../research/d10D8/sym2/haar_sym2 10 8 6409 108471 8 g3.txt psl 23 97 > g3.out 2>> g3.log`
- Card says nice -n 12 (common rules say nice -n 15 for grind); the card was followed.
- Files: g3.log (CHAIN lines), g3.out (RESULT), g3.ckpt (best set, one chain's best), g3.txt (solution, not written: no cost 0).
- Helper: mon.sh (counts CHAIN minima from g3.log).

## Final counts (run ended 03:24:28 UTC)

- RESULT: `d=10 D=8 group=psl 23 x Z_97 N=588984 best=12 evals=12072009 time=6409.0`. Plain RESULT best 12 means ORBW=3 units.
- Completed chains: 137 (CHAIN lines); mean chain about 47 s; about 1,880 evaluations/s at about 58 % CPU.
- Chain minimum (ORBW=3 units): best 12 (3 chains), median 21, <=12: 3, <=9: 0, <=6: 0, <=3: 0.
- Histogram (min:count): 12:3 15:11 18:45 21:48 24:28 27:2.
- The unfinished last chain at the stop was not logged as CHAIN.

## Rules applied

- Chain min <= 6 (scoreboard line) and <= 3 (EXDESC on its set): never triggered, so no EXDESC run and no CLAIM.
- Scoreboard: one line at 02:03 UTC (first result, best 12, ORBW=3). No new best after that.
- No cost 0 at any time; no solution file.

## Finding

- Same picture as the c1-grind runs: the wall-clock schedule (COOL, REHEAT in seconds) under load (4-5 busy cores) gives
  a median chain min of 21 and a best of 12 over 137 chains. Pooled grind data (c1 NOTES) says P(min <= 9) about 1 in 90
  per descent on psl. Here 0 of 137 at <= 9. Consistent, not significant.
- Not a new record candidate. Not added to any pooled tail.

## Log

- 01:37 launched g3 (seed 108471, pid 31655 timeout, 31657 scorer). First chain done in about 40 s.
- 01:54 chains 19, best 12. 02:03 chains 31, best 12. Scoreboard first-result line written at 02:03.
- 02:12 chains 44, 02:28 chains 66, 02:37 chains 78, 02:45 chains 89, 02:54 chains 101, 03:03 chains 113 (best 12 throughout).
- 03:12 chains 122, 03:21 chains 134, 03:24:28 run ended by its budget, RESULT written. Final: chains 137, best 12.

## Next steps if someone continues this

- Nothing running from this worker. The same run with seed 108472 and a step-based schedule (VCLOCK / MAXSTEPS) would
  remove the load-dependent schedule effect (see c1-grind NOTES).
