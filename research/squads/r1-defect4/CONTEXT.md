# Squad r1-defect4: bipartite (k,3,−4)-graphs

Lead: optimal-sat Opus session (branch claude/optimal-sat-nx83w2), 2026-10-25.

## Problem

A bipartite (k,3,−4)-graph: bipartite, maximum degree k, diameter 3, 2(k²−k−1) vertices (Moore bound minus 4).
For k ≥ 5 it is k-regular (Prop. 3.1 of arXiv:1203.3588), so it has n = k²−k−1 "points" and n "lines", every point
on k lines and every line through k points, and **diameter 3 ⟺ every two points share at least one line and every
two lines share at least one point.**

Known: k = 5 exists (unique, 38 vertices); k = 6 and k = 7 do not exist (Feria-Purón, Miller, Pineda-Villavicencio,
Discrete Math 2013, by hand). k ≥ 8 is open (conjectured: none). k = 11 and k = 15 matter for the degree–diameter
table: excluding them would lower the upper bounds for (11,3) and (15,3).

## Facts you can use (all proved)

- N = point–line incidence matrix (n×n). NNᵀ = (k−1)I + J + R_X where R_X is symmetric, nonnegative integer, zero
  diagonal, every row sum 2: c(x,y) = number of common lines of points x ≠ y = 1 + R_X[x][y]. So R_X is the adjacency
  matrix of a 2-regular multigraph on the points ("repeat graph"): disjoint cycles, and "digons" (two points with 3
  common lines). Same for lines: NᵀN = (k−1)I + J + R_Y. R_X and R_Y have the same spectrum.
- If points x, y share exactly two lines ℓ, ℓ', then ℓ, ℓ' share at least two points (x and y).
- Identity: for a point a on a line ℓ and any line ℓ': Σ_{lines L ∋ a} |L ∩ ℓ'| = Σ_{points b ∈ ℓ'} c(a,b)
  (with c(a,a) = k if a ∈ ℓ'). Consequence: if ℓ and ℓ' share exactly two points, every point a of ℓ outside ℓ ∩ ℓ'
  has a "repeat" on ℓ' (a point b ∈ ℓ' with c(a,b) ≥ 2).
- In the unique k = 5 graph both repeat graphs are a single 19-cycle (so there is no small local "quad" structure).

## What already exists

- Baseline CNF: `research/projects/optimal-sat/defect4/enc_d3m4.py k out.cnf` (normal form: point 0 on lines 0..k−1,
  line 0 through points 0..k−1). kissat: k = 5 SAT in 1.2 s, k = 6 not finished in 10 min.
- For inspiration only: the defect-2 case was cracked by a structure theorem that shrank the problem
  (`research/projects/optimal-sat/SUMMARY.md` §1).

## Scorer

`research/squads/r1-defect4/score.sh <your gen.py>`: runs `python3 gen.py k out.cnf` then kissat for k = 5 (must be
SAT), k = 6 (must be UNSAT, 900 s limit) and, if k = 6 took < 300 s, k = 7 (must be UNSAT). Prints a JSON line;
score = seconds (k = 6, plus k = 7 if done), lower is better; invalid answers score 99999.
Solver binaries: kissat `/tmp/claude-0/-home-user-degree-diameter/4905f117-080d-5578-b5d8-53a7377d03a3/scratchpad/kissat/build/kissat`,
cadical `.../scratchpad/cadical/build/cadical`. Python has `pysat` (python-sat) and `numpy`, `networkx`.

## Rules (shared machine: about 1 core for the whole squad, the lead's solvers use the rest)

- THREADS=1; run anything heavier than a second as `timeout 900 nice -n 10 <cmd>`; at most about 1.5 GB memory.
- Work only in your folder `research/squads/r1-defect4/<card>/`. No git commits. No edits anywhere else.
- **Soundness first:** every constraint you add must be either a proved consequence of the definition or a valid
  symmetry-breaking constraint (any graph can be relabelled to satisfy it). Explain why in a comment next to it.
  An unsound speed-up is worth nothing.
- Time box: about 15 minutes of work.
- Report: append ONE line of JSON to `research/squads/r1-defect4/scoreboard.jsonl`:
  `{"card": "c3", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <seconds or 99999>,
  "valid": true|false, "next": "<one line>"}` and reply to the lead in at most 5 lines.
