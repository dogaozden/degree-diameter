# Card w1 (round 4)

Read ../r1/PREAMBLE.md, ../r3/PREAMBLE.md and ../r4/PREAMBLE.md first. Your folder: research/squads/hunt-d5/r4/w1/ (create it).

(9,5) pattern-then-fill: in Z53 ⋊ Z26 an S is a j-pattern (the Z26 parts, a multiset) plus a-values. Collect the j-patterns of the cost ≤ 4 near misses (farm with SAVEBEST; files from cards c1/c2 may appear in ../c1, ../c2), then write an annealer that keeps one good j-pattern fixed and searches only the a-values (cost via the mt_53_26_16 table; index = a·26 + j). Is the cost lower than free annealing at equal CPU?
