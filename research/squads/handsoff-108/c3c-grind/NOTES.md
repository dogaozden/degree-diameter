# c3c-grind (worker c3c, squad handsoff-108)

Card: one more fresh-seed F15W3 grind on psl 23 97, until 03:25 UTC (relaunch of slot c3, 01:40 UTC).
Seeds 108471-108480 (restart = next seed). Start 01:37 UTC.

## Run

- Command (same as c1-grind g1, card seeds/nice): `ORBIT="3 3 1" RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=3 CKPT=g3.ckpt THREADS=1
  nohup nice -n 12 timeout 6469 .../research/d10D8/sym2/haar_sym2 10 8 6409 108471 8 g3.txt psl 23 97 > g3.out 2>> g3.log`
- Scorer budget 6409 s, timeout 6469 s: both end by 03:25 UTC (budget 03:24:00, hard stop 03:25:00).
- Card says nice -n 12 (common rules say nice -n 15 for grind); the card was followed.
- Log: c3c-grind/g3.log (CHAIN lines), out: g3.out (RESULT at end), ckpt: g3.ckpt, solution (only on cost 0): g3.txt.
- Launched pid 31655 (timeout), scorer pid 31657, at 01:37:11 UTC.

## Rules applied

- Chain min is in ORBW=3 units (multiples of 3). Chain min <= 6 (i.e. 3 or 6): scoreboard line. Chain min <= 3: EXDESC=1 on
  that chain's set (CKPT file with that set, in this folder). Cost 0: copy to records/, shared/check.sh, CLAIM line.

## Counts (refreshed at each check)

02:03 UTC: chains 31, best 12 (1 chain), median 21, <=12: 1, <=9: 0, <=6: 0, <=3: 0.
Histogram (min:count): 12:1 15:3 18:10 21:8 24:9.
02:12 UTC: chains 44, best 12, median 21, <=12: 1, <=9: 0, <=6: 0, <=3: 0 (hist 12:1 15:3 18:14 21:12 24:13 27:1).
02:37 UTC: chains 78, best 12, median 21, <=12: 1, <=9: 0, <=6: 0, <=3: 0 (hist 12:1 15:4 18:24 21:24 24:24 27:1).

## Log

- 01:37 launched g3 (seed 108471). First chain running.
- 01:54 chains 19, best 12. 02:03 chains 31, best 12. No scoreboard line yet (threshold is <=6).
- 02:03 scoreboard: first-result line (best 12, ORBW=3).
- 02:28 chains 66, best 12. 02:37 chains 78, best 12.
- 02:12 chains 44, best 12. Mean chain about 36-46 s. Process alive (pid 31657, RSS 12 MB, 58 % CPU).
