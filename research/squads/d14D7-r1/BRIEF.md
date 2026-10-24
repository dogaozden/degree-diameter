# Squad brief: cell (14,7), round 1

Goal: a bipartite graph of maximum degree 14 and diameter 7 on MORE than 1,771,560 vertices (table value; bipartite
Moore bound 10,458,086). Opus (session cell-14-7) runs this squad; you are one card. Work only in your card folder
`research/squads/d14D7-r1/<card>/`. No git commits. Never contact anyone or post anything outside the repo.

## What is known (read this, it saves you time)

- The table graph (Delorme-Gomez-Quisquater) is the "(2j+1)-fold polygon cover": take the incidence graph of the
  generalized hexagon GH(q) (split Cayley hexagon H(q); 2(q^6-1)/(q-1) vertices, (q+1)-regular, diameter 6, girth 12),
  add j perfect matchings sigma_1..sigma_j from points to lines, and lift by Z_{2j+1}: polygon edges voltage 0,
  matching t voltage t. Diameter 7 for ANY matchings. (14,7) = q=11, j=2: 5 x 354,312 = 1,771,560.
- Random-like Haar/Cayley graphs cannot reach the table here (size law: about 1.0-1.07M at best).
- NEW (this session): one copy MORE than 2j+1 is possible at small q. GH(2)+1 matching over Z4 has diameter 7
  (504 vertices, all-pairs VALID). Random matchings already come close for j=2 over Z6 at small q:
  misses per source (out of 6*|P| same-colour targets) with random matchings, hop voltages {1,4} in Z6:
  q=3: ~0.015, q=5: ~34, q=7: ~850, q=11: ~27,600 (13,000 with a random Z2 twist on polygon edges, GHV=z2).
  With hop voltages {1,4} the missing element 3 = 1-4 = 4-1 is reached by "out on one matching, back on the other"
  walks; {1,2} is about twice worse.
- So the targets are: GH(11)+2 matchings over a group of order >= 6 (2,125,872 vertices), or GH(9)+4 over order >= 14
  (1,860,040), or GH(8)+5 over order >= 24, or GH(7)+6 over order >= 46 (1,803,936; random misses ~5,000/source),
  or something else entirely. The same lifts at smaller q are records in other D=7 cells (e.g. GH(5)+2 over Z6 =
  46,872 at (8,7), above our 43,344; GH(7)+2 over Z6 = 235,296 at (10,7), above the table 224,694).

## Tools (all in research/cell147/, already compiled; data/ has GH(q) for q = 2,3,5,7,11,13)

- `gh_build q COORDS > gh_q.txt`: H(q), q prime. File: "P q", then P lines (one per hexagon line) with its q+1 point
  indices. Points are 0..P-1, lines P..2P-1 in the lift tools. COORDS: point index -> Tits coordinates (x0..x6 mod q,
  quadric x0x4+x1x5+x2x6 = x3^2).
- `glift GHFILE j D seconds seed OUT` (env options at the top of glift.c): annealer/evaluator for lifts of
  GH(q)+j matchings by a group of order m <= 64. Key env: GROUP ("cyc m", "ab a b", "dih n", "tab FILE"),
  HT (hop voltages, e.g. "1 4"), GHV (0 | z2 | free: polygon-edge voltages), HV (dgq | free), SIGMA (free | fixed),
  SAMPLE (sources per evaluation), T0/TEND, THREADS, INIT (start state), EVAL=1 (evaluate once; with SAMPLE uses a
  random sample), EDGES=file (with EVAL=1: write the lift edge list).
  Cost = number of (base source u, lift target (w,g)) at distance > 7 (same colour: > 6). 0 = diameter <= 7.
  Example: `GROUP="cyc 6" HT="1 4" EVAL=1 SAMPLE=100 ./glift data/gh_5.txt 2 7 0 1 /dev/null`
- `apsp EDGES d D`: independent all-pairs check of an edge list (prints RESULT VALID d=.. D=.. n=..).
- `ghtools.py`: Python helpers (load GH, BFS, read glift state files).
- Other repo tools: research/frontier/build_haar2.py (Haar checker), research/structured/ (orbit Haar search, on
  branch origin/claude/structured-search-orbit-w5dd4f), research/lifts/LITERATURE.md and RESULTS.md on branch
  origin/claude/voltage-lifts-search-6lfotq (polygon covers, negatives), research/theorems/squad165/ on branch
  origin/claude/beat-16-5-squad-jiiwg2 (building scans, route-chart lifts). Read files from other branches with
  `git show <branch>:<path>`.

## Machine rules (4 cores, 15 GB shared by 16 cards and Opus)

- Every run longer than ~20 s goes through the slot semaphore:
  `/home/user/degree-diameter/research/squads/bin/heavy.sh SECONDS <command...>` (it adds timeout and nice, and
  waits for one of 3 machine-wide slots). THREADS=1. At most ~1.5 GB memory per run.
- Your compute budget is stated on your card. Time box: about 20 minutes of wall clock in total.
- No edits outside your card folder. No git.

## Report

Append ONE line of JSON to research/squads/d14D7-r1/scoreboard.jsonl:
{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <number>, "unit": "<what the score is>",
 "valid": true|false, "next": "<one line>"}
and reply to Opus in at most 5 lines. A claim of a record must come with a file Opus can check (edge list or glift state
file plus the exact command).
