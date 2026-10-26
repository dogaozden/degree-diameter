# r4-c6: tail analysis of the descent statistics (card report, filed by the lead)

The card could not write files outside its scoreboard line, so this is its final report as sent. Reproduce with
`python3 -I research/squads/d10D8-r4/c6/analyze.py` (logs as of 11:43 UTC).

1. Estimated CPU-hours to the first cost-0 descent for the best tested policy (F15 on PSL(2,7) × SL(2,8) × Z7):
   35 (range 6 to about 1300 across tail models).
2. Fresh-descent minima: prod n = 264 (F10 169, F15 69, others), psl23 n = 31; minimum 8 (prod) and 9 (psl23), medians
   18–21. P(min ≤ 9) = 2/264 (prod), 1/31 (psl23); P(min ≤ 12) = 8/264 (prod), 3/31 (psl23).
3. P(min = 0) per fresh descent about 1e-4 (pooled least-squares fit of log CDF 1.4e-4; 5e-6 to 1e-3 across models).
   CPU-hours per descent: F10 0.0067, F15 0.0141, F30 0.019, F60 0.027, RESTART 0.052.
4. Re-descents from a chain's best do not beat fresh descents per CPU-hour (prod 2/11 vs 13/249; psl23: 26 of 32
   re-descents return to the same best); RESTARTAFTER=1/2 chains gave no improvement (prod 0/33, psl23 1/14).
5. 50 % of prod minima (26 % psl23) are not multiples of 3, i.e. contain uncovered α-fixed elements; 10 of 18 finished-run
   bests are not multiples of 3.
Tail counts at ≤ 10, 12, 15, 18 out of n: F10 1, 2, 13, 46 of 169; F15 0, 3, 13, 27 of 69; psl23 F30 1, 1, 4, 7 of 10;
psl23 RESTART 1, 1, 5, 11 of 18. Log-linear P(0): F15 7.6e-4 (18 CPU-h), F10 2.6e-5 (260 CPU-h, noisy), pooled prod
1.35e-4. Caveats: live logs; older cycle minima come from 30-second progress prints.
