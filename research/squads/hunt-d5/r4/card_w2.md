# Card w2 (round 4)

Read ../r1/PREAMBLE.md, ../r3/PREAMBLE.md and ../r4/PREAMBLE.md first. Your folder: research/squads/hunt-d5/r4/w2/ (create it).

(7,5) or (9,5) population search: build a pool of near misses (farm with SAVEBEST on Z41 ⋊ Z15 or Z53 ⋊ Z26), and write a genetic algorithm (crossover = union of two parents' S, then pick Δ elements greedily by marginal coverage; mutation = 1-swap), scored with haar5 eval or your own C. Report whether it beats the farms' cost distribution.
