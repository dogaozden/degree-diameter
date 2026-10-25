# Squad d12D8 round 2: common instructions (read fully before starting)

**Job:** bipartite graphs of maximum degree 12 and diameter 8 (cell (12,8)). The published table value is 4,650,100.

**New fact from round 2 (Opus, 2026-10-25):** the table value comes from J. Gómez's PhD thesis (UPC 1986), section
2.9.3, construction "ΩB₁" with B₁ = incidence graph of the generalized hexagon H(9). The thesis is at
/tmp/claude-0/dl/Gomez1986-PhD-red.pdf (scanned, 161 pages; thesis page P is PDF page P+6; §2.9.3 is thesis pp. 43–46 =
PDF pp. 49–52). Render pages with `pdftoppm -r 110 -f 49 -l 52 -png -gray <pdf> <prefix>` and look at the PNGs with
the Read tool. Built as Opus reads it, ΩB₁ has diameter **9**, not 8 (all-pairs at q = 3 and q = 5, BFS at q = 9): a
"new" vertex (degree 2α) is adjacent to copies of one base vertex t in only 2α of the 5α copies, so it is at distance
1 + 2 + 6 = 9 from the vertices opposite t in the other copies. If this holds, the table's (12,8) value is not a valid
graph, and the job becomes: find the largest VALID (12,8) graph (and check the claim independently).

Current best valid (12,8) graph from this job: Haar graph on SL(2,29) × Z79, 3,848,880 vertices (orbit search
ORBIT="3 4 0"); higher rungs are running on Opus's cores.

## Tools
- Hexagon H(q), q = 3, 5, 7, 9: `/home/user/degree-diameter/research/d12D8/hex/hex_q{q}.bin`. Python:
  `sys.path.insert(0,'/home/user/degree-diameter/research/d12D8/tools'); from hexlib import load_hex; n, lines = load_hex(q)`
  → `lines[l]` = the q+1 point ids on line l (points and lines both 0..n-1). Edge colourings (q+1 perfect matchings):
  `np.load('/home/user/degree-diameter/research/d12D8/hex/col_q{q}_s1.npy')[l, k]` = colour of edge (lines[l][k], l).
- **Exact all-pairs checker** (any graph, up to ~300k vertices in a few minutes): `/home/user/degree-diameter/research/d12D8/r2/apsp EDGES 12 8`
  where EDGES is a text file: first line = number of vertices, then one edge "a b" per line (0-based). It prints
  `diameter=` and `RESULT VALID/INVALID`. Single source BFS for big graphs: `/home/user/degree-diameter/research/d12D8/r2/eccs EDGES s1 s2 ...`
  (eccentricity and counts per distance).
- Lift checkers in /home/user/degree-diameter/research/d12D8/tools (liftcheck, affcheck) and r2 (classcheck, gencheck): read their headers.
- Haar search: `/home/user/degree-diameter/research/structured/haar_sym` (README in research/structured/README.md, §haar_sym and
  ORBIT); group lists: `python3 /home/user/degree-diameter/research/structured/tools/orb_screen.py 12 8 LO HI "k m f" --list`;
  independent check of a Haar solution file: `python3 /home/user/degree-diameter/research/frontier/build_haar2.py SOL.txt`.

## Machine rules (4 cores and 15 GB shared with Opus, who runs 2 heavy jobs)
- Single thread: THREADS=1, OMP_NUM_THREADS=1. Prefix heavy commands with `nice -n 10 timeout 1500`.
- At most ~1.5 GB memory per process. Only cards c3 and c4 may run a long heavy search (one process each at a time).
- No git commands. Write only inside your folder /home/user/degree-diameter/research/squads/d12D8_r2/cN/. Delete
  generated edge lists > 20 MB when done (keep generators and logs).
- Time box: about 25 minutes of work.

## Report
1. Append exactly ONE line of JSON to /home/user/degree-diameter/research/squads/d12D8_r2/scoreboard.jsonl:
   `{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact command>", "score": <largest VALID
   vertex count you produced, or null>, "valid": true|false, "finding": "<one line: the main fact you established>",
   "next": "<one line>"}` (use `echo '...' >> file`; one line, valid JSON).
2. Reply in at most 6 lines: the main fact, the evidence (commands and outputs), what failed.
