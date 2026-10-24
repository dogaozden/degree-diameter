# Squad round 4 (job cell-13-7): orbit unions, at q = 11 and at the other hexagon cells

Round 3's winner (card c3, research/squads/d13D7_r3/c3/): a set of 720 pairwise-opposite points of H(11) as a union of
orbits of a group <a, b> of isometries of Q(6,11): a of order 15 acting on a 5-dim subspace U, b of order 5 acting on
the 2-dim U^perp, commuting; the exact maximum-weight clique of the orbit graph is 720 (was 397 by LNS). Code there:
run_groups.py, orbl.py, wclq2.c (exact weighted branch and bound + tabu), replay2.py, fastlift.py, liftscan.py,
runlog.jsonl (every group tried), best_gen.txt, gens/. READ that code first and reuse it.

Why it matters: every pairwise-opposite point set R of H(q) adds vertices to a table cell built from copies of H(q):
- q = 11: (13,7) +2|R| (now 1,062,936 + 1,440), (14,7) +4|R|, (15,7) +6|R|.  Goal: beat 720.
- q = 13: (16,7) +4|R|; current best R = 168 (plain local search, research/d13D7/q13/R168_q13_idx.txt).
- q = 7: (9,7) +2|R|; current 172 (research/d13D7/q57/R172_q7_idx.txt).  q = 5: (7,7) +2|R|; current 58
  (research/d13D7/q57/R58_q5_idx.txt).  Upper bound for all: q^3 + 1 (not attained for q prime > 3).
Points of H(q) = points of Q(x) = x0x4 + x1x5 + x2x6 - x3^2 = 0 in PG(6,q); opposite iff
B(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3 != 0 (mod q, q prime here). Hexagon files (hexgen.c format, header
int32 q, N, L; L*(q+1) int32 line point indices; N*7 uint8 coordinates, points sorted by code sum x_i q^i, first
nonzero coordinate 1): research/d13D7/hex/hex_q5.bin, hex_q7.bin, hex_q11.bin, hex_q13.bin.

Scorer: `research/d13D7/tools/oppcheck research/d13D7/hex/hex_qQ.bin P FILE` (BFS test, valid for every q; ignore its
"criterion" line for q != 11 if it complains) -> `RESULT VALID pairwise_opposite m`.

Rules (shared machine, 4 cores; Opus is running big graph checks): at most ONE heavy process at a time per card,
single thread, `timeout 900 nice -n 10`, internal CPU limit <= 600 s per run, <= 1.5 GB, no git, write only in
research/squads/d13D7_r4/<card>/. Save your best as <card>/best_idx.txt (point indices) and its generators.
Append ONE JSON line to research/squads/d13D7_r4/scoreboard.jsonl:
{"card": "cN", "q": Q, "idea": "...", "code": "...", "command": "...", "score": m, "valid": true|false, "file": "...", "next": "..."}
and reply in at most 5 lines. Time box about 30 minutes.
