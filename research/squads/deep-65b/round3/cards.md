# deep-65b round 3 cards (Opus-written, 4 Haikus): beyond 704

## State
Record so far: 704 (split family, [[1,5],[5,1]] lift by C11 x M16 = 176_23; also a cyclic Z88-lift of an 8-vertex base,
records/build_d6D5_n704_z88.py). Round 2 (tabu, 8-12 s per seed): order 180 best cost 5, 183 best 7, 186/189 8,
order 192 best 6 (192_865, 192_909; Opus is running the EXACT search on 865, 909, 544, 105, 106 and on 180_21), 195-200
13+. The split family looks saturated near m = 176, so this round tries (a) more seeds where it was closest and (b) two
new structures next to it.

## Common rules
As in research/squads/deep-65b/round2/cards.md ("Common rules"), with: folder research/squads/deep-65b/round3/<card>/,
scoreboard research/squads/deep-65b/round3/scoreboard.jsonl, time box 45 minutes, goal n > 704. The faster tabu is
research/squads/deep-65b/round2/c6/tabu15f (same usage and output as shared/tabu15, 3.3x faster; build it into your
folder from round2/c6/tabu15f.c if the binary is missing).

## c1: split + hub orbits (mcos), n = 728
mcos (research/squads/deep-65b/prior/shared/mcos.c; header explains TYPE and N) anneals multi-orbit coset graphs.
Two new types next to the split family, where some degree goes to hub orbits (stabiliser C6, i.e. hubs joined to
the 6 vertices of a coset):
 (i) TYPE="1,1,6|1,1,6" N="1,4,1,5,1,0,0,1,0" (A0: 1 to B0, 4 to B1, 1 hub; A1: 5 to B0, 1 to B1; the A-hubs: one
     coset of B1), n = 4m + m/3, m = 168 (728) and 174 (754): groups with an element of order 6.
 (ii) TYPE="1,1,6,6|1,1,6,6" N="1,4,1,0,4,1,0,1,1,0,0,0,0,1,0,0" (every regular orbit gives one degree to its own hub
     orbit), n = 4m + 2m/3, m = 156 (728).
Check first that mcos accepts the types (it prints the orbit sizes; n must be as stated) and that its output graph
(EDGES=) scores the same with shared/score65. Calibrate mcos as in deep-65: TYPE="1|1" on SmallGroup(342,12) with
SEED=4 should reach cost 0 in about 20 s. Then screen the non-abelian groups of order 168 (type i) and 156 (type ii),
SECS=15 per class combination, MAXCOMB=4, one seed; deep runs on the best 3. Report best cost per type and order.

## c2: order 180, many seeds with the faster tabu
Take the 10 best order-180 groups from research/squads/deep-65b/round2/c1/ (its table or raw.txt; if missing, use
round1/c1/ranking.tsv), skip 180_21, 180_6 and 180_13 (Opus's exact search covers them), and run tabu15f seeds 1..20 x
10 s on each. Report best per group and any zero (check it at once).

## c3: order 192, many seeds with the faster tabu
Groups: 192_845, 931, 900, 168, 934, 916, 58, 171, 861, 22, 351, 978 (round 2's next best; Opus runs the exact search
on 865, 909, 544, 105, 106). Export them (tools/gap_fast.g, tables only) into your folder, then tabu15f seeds 1..12 x
12 s each. Report best per group and any zero.

## c4: cyclic lifts of the 8-vertex split base (new: general voltages)
The record is a Z88-lift of an 8-vertex base (records/build_d6D5_n704_z88.py prints its 24 darts and voltages).
Base, rows A0^0, A0^1, A1^0, A1^1, columns B0^0, B0^1, B1^0, B1^1 (edge multiplicities):
[1,0,3,2], [0,1,2,3], [2,3,1,0], [3,2,0,1]. In the record the voltages on the j = 1 copy are 45 x those on the j = 0
copy (a group lift); here allow ALL voltages. Write a cyclic-lift evaluator for this base (Z_n voltages; diameter 5 iff
from each of the 8 base vertices every same-side vertex is reached within 4 and every other-side vertex within 5; for an
abelian voltage group you can work with sums; check it with score65 on random voltages), a tabu over single voltage
changes, and: (1) calibrate at n = 88: the record's voltages must give cost 0; then from random starts, report how often
tabu reaches 0 at n = 88 in 30 s; (2) run n = 89, 90, ..., 100 (n = 712-800), several seeds each. Also try the other
split bases with p, q in {1,..,4}: rows [1,0,p,5-p], [0,1,5-p,p], [q,5-q,1,0], [5-q,q,0,1]. Report best cost per n.
