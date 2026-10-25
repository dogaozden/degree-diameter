# Squad d16D7 r2: maximum independent sets in two orbit graphs of H(13)

Goal: the bipartite (16,7) record. A new construction (cell-16-7 resume session; research/squads/cells/d16D7/typed5.c,
typed5s.c) gives 4,022,340 + 2·61·K vertices, where K = min(K_pts, K_lines) and K_pts / K_lines are the sizes of
independent sets in two "orbit graphs" (orbits of an order-61 collineation of the generalized hexagon H(13); vertex =
orbit with no two collinear members; edge = some members collinear). Current best: K_pts = 224, K_lines = 227, so
K = 224 and n = 4,049,668 (previous record 4,025,508). **Every extra orbit in min(K_pts, K_lines) is +122 vertices.**
Hoffman-type ceiling: about 470 orbits; 60% of it (~280) would be +6,800 vertices over today.

## The two problems (same kind, different graphs)

    /home/user/degree-diameter/research/squads/d16D7_r2/og_pts.txt     6504 vertices, 577,152 edges (avg degree 177)
    /home/user/degree-diameter/research/squads/d16D7_r2/og_lines.txt   6504 vertices, similar

Format: first line `M E`; then one line per vertex `idx rep deg n1 n2 ... n_deg` (idx = 0..M-1, rep = an element id you
can ignore, then the neighbour indices). A solution = a text file with one vertex index per line. Seeds (the current
best, 224 and 227): `seed_pts.txt`, `seed_lines.txt` in the same folder.

Scorer (exact; run it on every result you report):

    python3 /home/user/degree-diameter/research/squads/d16D7_r2/ogscore.py og_pts.txt YOUR_SOL     -> VALID orbits=K ...
    python3 /home/user/degree-diameter/research/squads/d16D7_r2/ogscore.py og_lines.txt YOUR_SOL

Your card's score = min(K_pts, K_lines), so run your method on BOTH graphs (the same code, two runs) and save
`best_pts.txt` and `best_lines.txt` in your folder.

## Rules

- Work only in `research/squads/d16D7_r2/<card>/` (create it). Write C (gcc -O2 -march=native) or Python+numpy; C is
  much faster for local search on graphs this size. No git commands. Do not touch other folders.
- Every heavy run (anything over ~20 s) goes through the slot script, which waits for a free shared CPU slot and adds
  nice and a 1200 s timeout:
      /home/user/degree-diameter/research/squads/d16D7_r2/run_slot.sh ./yourprog args...
  Give each run a CPU-time budget of at most 420 s (pts) + 420 s (lines); use clock() or CLOCK_PROCESS_CPUTIME_ID, not
  wall time (the box is shared). One run per graph; a second only if the first finished and you have a clear fix.
  Memory per run under 1.5 GB. Single thread.
- When done, append ONE line of JSON to `research/squads/d16D7_r2/scoreboard.jsonl`:
  `{"card": "c3", "idea": "<one line>", "code": "research/squads/d16D7_r2/c3/<file>", "command": "<exact>",
  "score": <min of the two>, "pts": <K_pts>, "lines": <K_lines>, "valid": <true|false>, "next": "<one line>"}`
  (use `echo '...' >> scoreboard.jsonl`), and reply in at most 5 lines.
- "valid" must come from ogscore.py on your saved files.

Extra data (only if your card needs it): `data/hex_q13.bin` (H(13): int32 q, N, L, then L*14 int32 point ids per line,
then N*7 uint8 point coordinates), `data/g13o61_pts.bin`, `data/g13o61_lines.bin` (int32 permutations: the order-61
collineation g on points / lines; the orbit of element x is x, g(x), g(g(x)), ...; the orbit-graph vertex of x is the
vertex whose `rep` is the smallest element of x's orbit), `data/g13o183_pts.bin`, `data/g13o183_lines.bin` (an order-183
collineation h whose cube generates the same group as g, so h maps g-orbits to g-orbits: an automorphism of each orbit
graph of order 3 after factoring out g).
