# Card c1 (round 1)

Read ../r1/PREAMBLE.md first. Your folder: research/squads/hunt-d5/r1/c1/ (create it).

(9,5) Haar graphs with orbit-symmetric S, ORBIT="3 3 0" (three orbits of an order-3 automorphism, no identity:
this solved SL(2,11) in 0.5 s), every non-abelian group of order 1378..1400 that has an automorphism of order 3 with
few fixed points (≤ 40). `gapgroup.py table N I T.bin 3`; read the first number of each .aut3 line (fixed points);
for each usable α: `AUT=T.bin.aut3 ALINE=j ORBIT="3 3 0" haar5 anneal T.bin 9 10 SEED`, 2–3 seeds. Orders with many
groups (1392: 193, 1400: 147): rank by small centre first. Not yours: other orbit shapes (card c2).
