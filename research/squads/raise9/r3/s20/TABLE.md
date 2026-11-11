# s20 table: (20,9) groups above 1,972,000,272 vertices (N > 986,000,136)

Candidates from tools/pick2.py 20 9 13 18 200 r3 (N, 2N, mu):
- sl 997 n=1      N=991,025,976  2N=1,982,051,952  mu=13.80  r3=0
- sl 521 n=7      N=989,941,680  2N=1,979,883,360  mu=13.52  r3=2
- sl 479 n=9      N=989,115,840  2N=1,978,231,680  mu=13.30  r3=2
- sl 223 n=90     N=998,040,960  mu=15.78
- sl 233 n=79     N=999,279,216  mu=16.16
- sl 239 n=73     N=996,572,640  mu=15.35 (director runs it)

Measured (haar_big0 20 9, ORBIT "3 6 2", THREADS=1):

| group | ORBIT | mu | samples | min | p10 | median | note |
|---|---|---|---|---|---|---|---|
| sl 997 n=1 | 3 6 2 | 13.80 | 0 | - | - | - | no RANDORB sample finished |
| sl 997 n=1 | 3 6 2 | 13.80 | 0 | - | - | - | 3 attempts: 150 s, 100 s (killed), 98 s (killed) |

Not run: "3 5 5", the (group, ORBIT) pairs for sl 521 n=7, sl 479 n=9 (same blocker), "5 4 0" (haar_big0 hard-codes an
alpha of order 3: it aborts with "alpha^k != 1" for k = 5, so "5 4 0" needs a new choose_alpha; not done).

Blockers measured:
- Memory: the program itself prints "memory 1.50 GB" for N = 9.9e8, d = 20 (not ~500 MB). Cause: two bitsets
  (~0.51 GB) plus FR/FC/PS/PI per generator (24 R bytes x d = ~0.48 GB at d = 20). Cap of 600 MB for this card is not met.
- Time: the timeout 105 s did not stop the process (SIGTERM is only a flag; it kept running for 150 s). The sample did not
  complete under load 17-22 (4 cores): user CPU was 6.5 s in a 154 s wall run. Only `timeout -s KILL` ends it on time.
- Result: no cost value, no ranking. The "2-15 s per sample" in the card does not hold at this load.
