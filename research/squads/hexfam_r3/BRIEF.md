# Squad hexfam_r3 (project hexagon-family, Opus lead), 2026-10-25, round 3: evolve the EXTENSION idea

## What works now (read research/projects/hexagon-family/THEOREM.md, Lemma 3 and Proposition 4, the extension)
A freed set may contain points at distance 4 from each other, if the lines side mirrors it (Lemma 3). Concretely
(Proposition 4): take a record pure set R (pairwise opposite points) with lines S inside a spread Sp (pairwise
opposite lines), and ADD points x (pairwise opposite, none collinear with R) each with a line s_x (pairwise
opposite, not in Sp). For each r in R its pattern T(r) = {i : r is at distance 4 from x_i, i.e. B(r, x_i) = 0};
for each free spread line l its pattern T(l) = {i : l at distance 4 from s_i}; the spread line meeting s_i is
removed. Feasible iff for every pattern T: #{r : T(r)=T} <= #{free l : T(l)=T}. Every added point is worth graph
vertices: q = 11: 12, q = 13: 4, q = 5, 7, 8: 2.

Current bests (pairs files "r s" = freed point, its line; all in this folder):
| q | pure R | best total | file |
|---|---|---|---|
| 11 | 756 | **768** | best_q11_768.pairs |
| 13 | 792 | **815** | best_q13_815.pairs |
| 8 | 217 | **232** | best_q8_232.pairs |
| 7 | 288 | **296** | best_q7_296.pairs |
| 5 | 72 | **81** | best_q5_81.pairs |
R sets: research/d10D7/sets/P11_r6c7_756.txt, P13_E7sub_E6_792.txt, P8_r5c4_217.txt, P7_c5_288.txt, P5_c6_72.txt.
Spreads: research/d10D7/sets/L11_spread.txt, L13_spread.txt, L8_spread513.txt, L7_c5_344.txt, L5_c6_126.txt.
Code: research/projects/hexagon-family/ext/extend5.py (greedy: sampled lines, entropy tie-break), extend6.py (same,
candidates re-ranked by overlap penalty), mixsol.py (checker). The greedy stalls because R-points in two or three
of the sets N(x_i) need spread lines with the same pattern, and those cells are tiny.

## Scorer (the only thing that counts)
    python3 /home/user/degree-diameter/research/projects/hexagon-family/ext/mixsol.py Q PAIRS /tmp/scratch_prefix 1 3
It checks Lemma 3 independently (all distances, midpoint -> midline map), builds sigma, verifies (R2), and builds a
hub graph. Success = it prints "Lemma 3 holds: K = <total>" and "(R2) verified" and "wrote ...sol". K is the score.
(Use your card folder for the prefix, e.g. research/squads/hexfam_r3/c1/chk.)

## Tools
research/projects/hexagon-family/tools/q6lib.py (Geo: G.B polar form, G.LP points of lines, G.PL lines of points),
hex files in research/projects/hexagon-family/hex/. numpy, scipy, OR-tools CP-SAT available.

## Machine rules (4 cores, 15 GB, shared with 8 others and 2 Opus jobs)
One single-threaded process at a time; `timeout 1500 nice -n 10`; <= 1.5 GB. Work only in your card folder
research/squads/hexfam_r3/<card>/. No git. About 30 minutes. Save your best as best_q<Q>_<K>.pairs in your folder.

## Report
Append ONE JSON line per q to research/squads/hexfam_r3/scoreboard.jsonl:
{"card": "c1", "q": 11, "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <K>, "valid": true|false,
 "file": "<pairs path>", "next": "<one line>"}
then reply in at most 5 lines.
