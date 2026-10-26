# Card a2 (round 1)

Read ../r1/PREAMBLE.md first. Your folder: research/squads/hunt-d5/r1/a2/ (create it).

(5,5) Haar graphs, orders 208..224 (208: 46 groups, 210: 11, 212: 3, 216: 168, 220: 13, 222: 5, 224: 190).
Too many to do all: rank the non-abelian groups by small |G/G'| (= N/|G'|) and small centre (gapgroup.py list gives
|G'| and |Z|), screen the best ~60 with `haar5 anneal TABLE 5 6 SEED`, then spend the rest on the 5 best (more seeds,
orbit search with order-2/3/4 automorphisms: ORBIT="2 2 1", "4 1 1", and "3 1 2"). Not yours: orders < 208 (card a1).
