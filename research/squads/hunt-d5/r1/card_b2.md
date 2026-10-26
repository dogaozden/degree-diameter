# Card b2 (round 1)

Read ../r1/PREAMBLE.md first. Your folder: research/squads/hunt-d5/r1/b2/ (create it).

(7,5) Haar graphs at orders 608, 616, 624, 625, 630 (608: 188 groups, 616: 32, 624: 255, 625: 10, 630: 30).
Rank by small |G/G'| and small centre, skip groups with a central or abelian quotient of order > 50; screen the best
~50 with `haar5 anneal TABLE 7 8 SEED`; then orbit search (ORBIT="3 2 1", "2 3 1", "6 1 1") on the 5 best.
Not yours: the other orders 606–622 (card b1).
