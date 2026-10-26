# Card a1 (round 2)

Read ../r1/PREAMBLE.md and ../r2/PREAMBLE.md first. Your folder: research/squads/hunt-d5/r2/a1/ (create it).

(5,5) Haar graphs on metacyclic-type groups of orders 193..215 (a normal cyclic subgroup with a cyclic quotient:
C13⋊C3 × C5 (195), C67⋊C3 (201), C29⋊C7 (203), C41⋊C5 (205), C97⋊C2 (194), C7⋊C3 × C10 (210), …; find them with
`gapgroup.py list N`, structure "C… : C…"). For each: `OMP_NUM_THREADS=1 haar5 exh T.bin 5` (exact minimum over all S,
about 100 s at N = 200) — a minimum > 0 is a certificate, a 0 is a record. Do the 8 most promising (small |G/G'|).
