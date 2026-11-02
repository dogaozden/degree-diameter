start 23:16 UTC; cell (16,9) mu-window screen

## Idea (w05): cell (16,9), a window screen by random-orbit cost ratio
Cell (16,9) (record SL(2,101) x Z169, N = 174,103,800, mu 24.6) is not covered by any other card of round 2. Its mu-law
makes a raise cheap: a 1 % raise costs mu ~ 29. Window candidates with N in (174.1M, 176.1M] and mu <= 30 (pick.py 16 9 20 34 3 400):
psl 179x61 (N 174.92M, mu 26.6), psl 109x271 (175.46M, 28.0), sl 83x307 (175.51M, 28.2), sl 293x7 (176.07M, 29.7),
sl 97x193 (176.13M, 29.8). Screen: haar_big0 RANDORB=m with ORBIT "3 5 1" (random symmetric S, no search).
Metric: random median cost divided by mu (the record group's own ratio is the bar; lower is better).
Result: see the scoreboard line. Random-S median/mu: record SL(2,101)xZ169 60/24.6 = 2.44 (12 samples, min 32);
psl179x61 84/26.6 = 3.2 (15 samples, min 51); sl83x307 92/28.2 = 3.3 (12, min 54); sl293x7 72/29.7 = 2.42 (7, min 50).
Only sl293x7 matches the record's ratio. Annealing (haar_big0, ORBIT "3 5 1", 4 candidates per step, 1 thread, machine load ~21)
ran 25 evaluations over 3 chained runs: cost 82 -> 36 and stuck at 36 (about 17 s per evaluation under load).
Late add: sl97x193 random median/mu = 84/29.8 = 2.82 (8 samples, min 50). Ranking by ratio: sl293x7 2.42, record 2.44, sl97x193 2.82, psl179x61 3.2, sl83x307 3.3. Scoreboard line (written 23:28) reports sl293x7 as the lead; this late line is in IDEA.md only.
