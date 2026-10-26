# Card b1 (round 1)

Read ../r1/PREAMBLE.md first. Your folder: research/squads/hunt-d5/r1/b1/ (create it).

(7,5) Haar graphs, every non-abelian group of order 606..622 except 608 and 616 (about 60 groups).
`haar5 anneal TABLE 7 8 SEED` (two seeds) per group; then on the 5 best: orbit search with order-3 automorphisms
(`gapgroup.py table N I T.bin 3`, ORBIT="3 2 1") and order-2 (ORBIT="2 3 1"), several short seeds each. Not yours:
608, 616 (card b2), 623+ (card b2), lifts (b3, b4).
