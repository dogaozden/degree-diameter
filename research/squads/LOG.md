# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-25 06:43 UTC, optimal-sat lead (Opus), round r1-defect4

Goal: a fast, sound method for bipartite (k,3,−4)-graphs (scorer: k=5 SAT, k=6 and k=7 UNSAT, time to UNSAT), as a
step toward (11,3,−4) and (15,3,−4), which would lower the (11,3) and (15,3) upper bounds. Folder
`research/squads/r1-defect4/` (CONTEXT.md, score.sh, scoreboard.jsonl). Baseline (`enc_d3m4.py`): k=6 > 10 min.

Cards and best result (k=6 limit 900 s, machine heavily loaded while the lead's three k=11 solvers ran):
- c1 breadth-first normal form at point 0 (4 repeat cases) + lex-leader: k=5 SAT 0.9 s, **k=6 UNSAT 127 s**, k=7 timeout.
- c2 explicit repeat-graph variables + symmetry breaking: k=5 SAT, k=6 timeout.
- c3 split by cycle type of the repeat graph (determinant-filtered): k=5 all 29 types done (only the 19-cycle is SAT,
  matching uniqueness), k=6 has 221 types, not finished.
- c4 CP-SAT (OR-Tools, symmetry level 4): k=5 SAT 4.3 s, k=6 unknown at 880 s.
- c5 Haar graphs / near-difference sets: no report yet.
- c6 C backtracking with canonical star: k=5 found (3.4 s), k=6 not exhausted (first of up to 2,675 stars > 850 s).
- c7 wildcard encoding: k=5 SAT, k=6 timeout.
- c8 implied local rules from the repeat identity: k=5 SAT, k=6 timeout.

Kept: c1's normal form (the only valid score). Verdict: the squad reproduced the known k=6 result fast but nobody
reached k=7; with the table needing k=11 (109 points) and k=15, defect 4 at diameter 3 is out of reach with these
methods. Defect 4 has long repeat cycles (a single 19-cycle at k=5), so there is no small quotient like the defect-2
case. Next: none on this goal for now; the lead's compute stays on (11,3,−2).
