# Card a1 (round 3)

Read ../r1/PREAMBLE.md and ../r3/PREAMBLE.md first. Your folder: research/squads/hunt-d5/r3/a1/ (create it).

(5,5) exhaustive Haar search on order 216: rank the non-abelian groups of order 216 by small |G/G'| (gapgroup.py list 216 is slow: use your own GAP call printing only i, Size(DerivedSubgroup), Size(Centre)), then `../../tools/haar5 exhp T.bin 5 0` (about 10–20 s per group; exact: a cost-0 set cannot be missed) on as many as the budget allows, best-ranked first.
