# Card a3 (round 1)

Read ../r1/PREAMBLE.md first. Your folder: research/squads/hunt-d5/r1/a3/ (create it).

(5,5) lifts of 3+3 base multigraphs (5-regular bipartite, 6 vertices) over groups of order 65..75 (all groups:
abelian and non-abelian; 72 has 50 groups — pick the non-abelian ones with small centre). Our record 354 is a Z₅₉-lift
of K₃,₃ + two doubled matchings. Enumerate the 5-regular bipartite multigraphs on 3+3 vertices (K₃,₃ plus 2 extra
perfect matchings, or other multiplicity patterns; each vertex degree exactly 5), and run `flift BASE TABLE.bin 5 5 5
SEED` on each (base, group). Report the largest lift size with cost 0. Not yours: 2+2 and 4+4 bases (card a4).
