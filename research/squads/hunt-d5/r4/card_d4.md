# Card d4 (round 4)

Read ../r1/PREAMBLE.md, ../r3/PREAMBLE.md and ../r4/PREAMBLE.md first. Your folder: research/squads/hunt-d5/r4/d4/ (create it).

(6,5) NEW CELL farm + LNS on C3 × SL(2,5) = SmallGroup(360,51) (cost 4 in round 3): make the table with `gapgroup.py table 360 51 T.bin`, farm `SAVEBEST=1 haar_tab 6 5 10 SEED 16 OUT tab T.bin 1` (20 seeds), then `haar5 lns T.bin 6 "S" 2 120 1` and the exact 3-swap check `nbhd.py T.bin 6 "S" 3 0` on the best sets.
