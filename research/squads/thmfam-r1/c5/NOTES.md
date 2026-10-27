# c5 Transport the records (thmfam-r1)

Records (haar_ecc at own prime, lifted set reproduces the record exactly):
- d7D8_psl_19_14_orb3_s1 (psl 19, m 14, Delta 7): own excess 1.986 (diam 8). Lifts: lifts_d7D8.txt
- d6D9_sl_17_13_orb3f0_s2 (sl 17, m 13, Delta 6): own excess 2.127 (diam 9). Lifts: lifts_d6D9.txt
- d6D8_sl_13_7_s1 (sl 13, m 7, Delta 6): own excess 2.014 (diam 8). Lifts: lifts_d6D8.txt
- d7D9_psl_29_19_orb3_s1 (psl 29, m 19, Delta 7): own excess 2.106 (diam 9). Lifts: lifts_d7D9.txt

Lifting: lift.py (exact det 1 integer lifts, entries |x| <= 49; psl allows sign). gen_lift.py reduces the lifts mod q.

Family scores, q = 23..113 primes (22 each; all connected, no errors):
- d7D8 lifts: mean_excess 3.081 (range 2.47-3.67); no q reaches D=8 or 9.
- d6D9 lifts: mean_excess 3.243 (range 2.56-3.80); best D=10 0.698 of table.
- d6D8 lifts: mean_excess 3.083 (range 2.52-3.78); best D=10 0.754 of table.
- d7D9 lifts: mean_excess 2.865 incl. own q=29 (2.901 excluding q=29; range 2.45-3.43); D=9 at q=29 is the record itself (1.157 of table); D=10 at q=43 0.76 of table.

Reading: records stay at excess ~2.5-3.5 at other q, versus ~2.0-2.1 at their own q and ~3.2-3.5 for a random alpha-closed set. The
transported set beats random but loses most of the record quality; the record's goodness is specific to its (p, m).
Full JSON: score_<name>.json. Screen runs: 1-2 s each for q <= 53.
