# Card b2 (round 2)

Read ../r1/PREAMBLE.md and ../r2/PREAMBLE.md first. Your folder: research/squads/hunt-d5/r2/b2/ (create it).

(7,5) Haar graphs on every metacyclic-type group of order 606..660 (structure "C… : C…" or "(C… : C…) x C…"
in `gapgroup.py list N`; skip abelian), 3 seeds × 8 s each with `haar5 anneal T.bin 7 8 SEED`, then 10 more seeds on
the 5 best and `tools/exho_all.sh N I 7 "2 3 5 6"` (TMO=120) on the 3 best. Round 1 already did 606..622 with 2 seeds
(615/1: 4, 609/1: 8, 610/2: 8, 612/5: 9) — re-screen those only with more seeds.
