# Squad d12D8 round 1: common instructions (read fully before starting)

**Goal of the job:** a bipartite graph of maximum degree 12 and diameter 8 with MORE than 4,650,100 vertices.
The table value 4,650,100 (Delorme 1985) = 2·35·66,430: it is (we believe) a lift, by a group of order 35, of
"generalized hexagon H(9) incidence graph + 2 extra edges per vertex". H(9) has n = 66,430 points and 66,430 lines,
each line has 10 points, each point is on 10 lines, the incidence graph has girth 12 and diameter 6.
Random voltage assignments only reach group order ~12-14; Delorme reaches 35. We need order >= 36 at q = 9
(2·66,430·36 = 4,782,960), or other designs. Background: /home/user/degree-diameter/research/d12D8/README.md (read it).

## Tools (all in /home/user/degree-diameter/research/d12D8/tools; binaries are built)
- Hexagon files: /home/user/degree-diameter/research/d12D8/hex/hex_q{3,5,7,9}.bin. Load in Python with
  `sys.path.insert(0, '/home/user/degree-diameter/research/d12D8/tools'); from hexlib import load_hex; n, lines = load_hex(9)`
  → `lines` is an (n, q+1) int array: lines[l] = the q+1 point ids on line l. Points and lines are both 0..n-1.
  The .bin also stores 7 coordinates per point (PG(6,q) quadric x0x4+x1x5+x2x6 = x3²; see tools/hexgen.c for the
  file layout: int32 q, N, L; then L*(q+1) int32; then N*7 uint8 coordinates; field element index a + p*b for
  a + b*α with α² = a non-square mod p when q = p²).
- **Base file format** (text): first line `NP NL m cyc` (or `NP NL m table` followed by the m×m multiplication table,
  element 0 = identity), then one edge per line `p l g` (point p, line l, voltage g in 0..m-1). Parallel edges allowed.
  `hexlib.write_base(fn, n, edges, m)` writes it.
- **Scorer:** `OMP_NUM_THREADS=1 nice -n 10 timeout 900 /home/user/degree-diameter/research/d12D8/tools/liftcheck BASE 7 STEP`
  Lift = vertices (v, x), x in the group; (p,x) ~ (l, x·g). It BFSes from point sources (p, identity) (every
  STEP-th point) to depth 7 and prints `total uncovered (line,x) pairs`. 0 from ALL sources (STEP 1) means the lift
  has diameter <= 8. At q = 9 use STEP 331 (201 sources, ~3-5 s single thread) while exploring; STEP 1 takes ~10 min.
  Lift order = 2·n·m. Max group order 64.
- `nbwalks BASE src 7`: number of non-backtracking walks of length <= 7 from point src to each (line, group element).
- `mk_var.py q VARIANT m2 seed out`: hexagon + 2 hops with Delorme's Z_5 levels × random Z_m2 (CRT), VARIANT in
  rand | same | inc | inc1 | incsame (see README). `mk_rand.py`, `mk_xm.py`: other generators (read them).
- C compile: `gcc -O3 -march=native -o prog prog.c` (add -fopenmp only if needed, run with OMP_NUM_THREADS=1).

## Machine rules (4 cores and 15 GB shared by 17 agents)
- Single thread only: OMP_NUM_THREADS=1, THREADS=1. Prefix heavy commands with `nice -n 10 timeout 900`.
- At most ~1.5 GB memory. Keep individual runs short (< 2 min) except your one main run.
- No git commands at all. Write only inside your card folder /home/user/degree-diameter/research/squads/d12D8_r1/cN/
  (scripts, base files, logs). Large base files (> 20 MB): delete them when done, keep the generator + seed.
- Time box: about 20 minutes of work.

## Report
1. Append exactly ONE line of JSON to /home/user/degree-diameter/research/squads/d12D8_r1/scoreboard.jsonl:
   `{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact command to reproduce>", "q": <q>,
     "group_order": <m>, "sampled_misses_per_source": <number or null>, "score": <lift vertices with 0 misses on the
     check you ran, or null>, "check": "<STEP used>", "valid": true|false, "next": "<one line>"}`
   (use `echo '...' >> file`; one line, valid JSON).
2. Reply to the caller in at most 5 lines: the best number, what worked, what did not.
