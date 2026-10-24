# Squad brief: (14,7) round 3 — large partial ovoids inside the elliptic section E (q = 11)

You are one card of an 8-card Haiku squad run by Opus (session cell-14-7, second session). Machine rules, scoreboard
format and report format are as in research/squads/d14D7-r2/BRIEF.md (read its "Machine rules" and "Report" sections;
replace d14D7-r2 by d14D7-r3 everywhere). Work only in research/squads/d14D7-r3/<card>/. No git.

## The problem (everything you need)

Record status: (14,7) is now 1,772,180 = 1,771,560 + 4N with N = 155 flags per matching. Every extra flag is +4
vertices at (14,7), +6 at (15,7), +2 at (13,7). The flags come from a PARTIAL OVOID inside E:
- The split Cayley hexagon H(11) lives on the quadric X0X4 + X1X5 + X2X6 = X3^2 in PG(6,11) (Tits coordinates).
  E = the points with X4 = -X0 (an elliptic quadric Q^-(5,11), 15,984 points). The hexagon lines inside E form a
  spread: 1,332 pairwise opposite lines, each point of E on exactly one of them.
- A set S of points of E that are pairwise NON-orthogonal (B(x,y) != 0 with B(x,y) = x0y4 + x4y0 + x1y5 + x5y1 + x2y6
  + x6y2 - 2x3y3 mod 11) gives |S| valid flags (p, spread line through p). So: find a large independent set in the
  orthogonality graph on E (a strongly regular graph, 15,984 vertices, degree 1,342; equivalently a partial ovoid of
  Q^-(5,11)). Best known here: 155 (iterated local search, cell147/units/spreadpack.c). Upper bounds: 1,332
  (Hoffman); literature bounds for partial ovoids of Q^-(5,q) are around (q^3+q+2)/2 = 672.
- Files (in /home/user/degree-diameter/research/cell147/data/): E11.graph ("n m", then m edges "i j", vertices 0..15983
  = points of E), E11.map (line i: hexagon point id of vertex i, its spread line id, its 7 coordinates x0..x6),
  coords11.txt (coordinates of all 177,156 hexagon points, line = point id). Do not copy the 114 MB graph file; read it
  in place (or recompute orthogonality from coordinates, which is fast).
- SCORER: convert your independent set (vertex ids) to flags "point_id spread_line_id" (columns 1-2 of E11.map), then
  `cd /home/user/degree-diameter/research/cell147/units && CHECKONLY=1 ./pack ../data/gh_11.txt 0 1 /dev/null FLAGS`
  prints "VALID N flags". Your score is N.
