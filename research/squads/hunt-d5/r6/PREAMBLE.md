# hunt-d5 squad, round 6: preamble (read ../r1/PREAMBLE.md, ../r3/PREAMBLE.md and ../r5/PREAMBLE.md first)

Same rules as round 5 (THREADS=1, every run `timeout <s> nice -n 10`, about 10 CPU-minutes, 35 minutes wall clock, no
git, write only in `research/squads/hunt-d5/r6/<card>/`, one JSON line to `research/squads/hunt-d5/r6/scoreboard.jsonl`).
The machine is busy (director farms at nice 1), so expect about a third of a core; size runs accordingly.

State after round 5: (9,5) now 2,758 (Haar graph of Z197 ⋊ Z7, director farm seed 40164; 1 cost-0 in about 180 seeds of
8 s, cost 2 in about 3 %). (7,5): director farms run on meta 41 15 10 1 (615), meta 29 7 16 3 (609), meta 61 10 9 1
(610); best cost 2 (615, 610). (9,5) director farm on meta 31 15 9 3 (1395, cost 4 in round 5). (6,5): SmallGroup(360,51),
(351,1), (351,5), (351,6), (351,7), (351,12), (355,1), (357,1) are proved to have no (6,5) Haar graph (exact search), so do
not spend time on them. (5,5): no Haar graph for orders 193–239 except a few groups still being searched (director).

For a group that is not metacyclic-type use GAP tables: `python3 ../../tools/gapgroup.py list N` (one line per group:
"N i abelian? |G'| |Z| structure"), `python3 ../../tools/gapgroup.py table N I T.bin`, then
`SAVEBEST=1 COOL=10 REHEAT=40 THREADS=1 timeout 30 nice -n 10 ../../tools/haar_tab d 5 SECONDS SEED 16 OUT tab T.bin 1`
(prints a RESULT line with best=COST; a cost-0 run writes OUT). GAP listing of an order with many groups is slow: list
once into a file, never in a loop.
