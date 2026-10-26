# Card a1 (round 1)

Read ../r1/PREAMBLE.md first. Your folder: research/squads/hunt-d5/r1/a1/ (create it).

(5,5) Haar graphs, every non-abelian group of order 193..207 (about 80 groups; order 200 has 46).
Method: `gapgroup.py list N` for each N; screen every non-abelian group with `haar5 anneal TABLE 5 6 SEED` (two seeds);
then the 4 lowest-cost groups get `haar5 exh` (exact minimum, ~100 s each) — an exact minimum > 0 is a certificate.
Also try orbit search on the best groups: automorphisms of order 2 (ORBIT="2 2 1") and 4 (ORBIT="4 1 1").
Not yours: orders ≥ 208 (card a2), lifts (a3, a4).
