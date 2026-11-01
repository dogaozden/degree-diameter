# Job beyond-small, squad round 1 — common header (read this first, then your card)

Director: Opus cloud session, branch claude/beyond-small-cells-fwb6si, 2026-11-01.

## Goal of the round: (17,5)

Find a **bipartite graph of maximum degree ≤ 17 and diameter ≤ 5 on more than 33,792 vertices**. 33,792 is the floor:
the (16,5) route-chart lift (degree 16) is already a (17,5) graph. Upper bound 139,804 (bipartite Moore bound − 6).
Any checked graph above 33,792 is a result, even 33,793. A value near 36k–40k would be excellent.

## Machine rules (4 cores and 15 GB shared by ~17 agents and the director)

- **Every Bash command must finish in under 110 s.** A longer command goes to the background and you sit idle. Chain
  short runs instead: write state to a file, resume from it. Use `timeout 100 nice -n 10 <cmd>`.
- One thread per process (no OpenMP/pthreads unless your card says so), at most ~700 MB of memory.
- Work only in your folder `research/squads/beyond-small/r1/<card>/`. No git commands. No edits elsewhere.
- Write C for anything inner-loop (gcc -O3 -march=native). Python is fine for setup and building edge lists.
- Do not end your work while a process you started is still running.

## Scorer (the only thing that counts)

Edge list format: first line `n`, then one edge `u v` per line, vertices 0..n−1.

    research/squads/beyond-small/bin/apsp EDGES 17 5        # all pairs, prints "RESULT VALID d=17 D=5 n=..."

It is fast (the 33,792-vertex (16,5) graph checks in under 1 s). Only a RESULT VALID line with n > 33,792 counts.
Keep any valid edge list in your folder as `best_n<n>.edges` (do not compress) and say how to rebuild it.

## Scoreboard (one JSON line when you stop, appended to research/squads/beyond-small/r1/scoreboard.jsonl)

    {"card": "c05", "idea": "<one line>", "code": "<path>", "command": "<exact rebuild/check command>",
     "score": <largest n with RESULT VALID, or 0>, "valid": true|false, "best_cost": <your search's best cost if no
     valid graph, else 0>, "next": "<one line: what you would try next>"}

Then reply to the director in at most 5 lines.

## Useful files

- (16,5) 33,792 graph: `research/squads/beyond-small/data/d16D5_n33792.edges` (already built; read-only), builder and
  full description `research/theorems/graphs/build_d16D5_n33792.py`. Vertex numbering: A-vertex ((a_i, g), x) →
  (22i + g)·256 + id(x), B-vertex ((b_j, h), y) → 16896 + (22j + h)·256 + id(y), id(x) = x0 + 4x1 + 16x2 + 64x3,
  F4 = {0,1,w,w²} coded 0..3, addition is XOR, multiplication table MUL in the builder. Controller: K3,3 with its
  perfect matching doubled, lifted by Z22 (66 + 66 controller vertices); lift edge ((a_i,g),x) ~ ((b_j,g+v),A_c x+λb_c),
  λ ∈ F4, letter c of the base edge. Theory: research/theorems/BEAT_16_5_SQUAD.md §2 (pencil lemma, theorem, how
  33,792 was found). The search tools of that job: research/theorems/squad165/ (mlift_chart.c, chart_search.c, charts/).
- Route chart over F5 that gave (20,5) 75,000: research/squads/beyond/r1/c04/ (chart5.c, mk5.py, zn20.txt).
- Plain-fifth-letter attempts at (17,5): research/squads/beyond/r2/d04/lift17.c, research/squads/beyond/r4/f01/lift17b.c
  (exact affine-coverage cost; reusable code for route-chart lifts with extra edges).
- Doubled-matching lifts of W(q): research/d10D7/DM_D5.md, research/frontier/beyond/MDM.md, research/d10D7/gqgen.c,
  dmfast.c.
- Haar-graph searchers: research/structured/haar_sym.c (orbit-closed S), research/selfdual-d5/ (self-dual sets, tabu).
- Previous job's notes on these cells: research/frontier/beyond/BEYOND_TABLE.md, research/squads/LOG.md.

## Already found / already ruled out (do not repeat)

- Floor 33,792 = (16,5) route chart (degree 16). LANL's (16,4) double cover gives 32,768 (not ours, below the floor).
- Polygon cover 7·|W(13)| = 33,320 (any 3 plain matchings, Z7) — below the floor.
- MDM / doubled-matching lifts need an EVEN number of extra degrees over W(q); with q = 13 (degree 14) the odd third
  degree adds no sheet. Blind Z8 lifts of W(13) with 3 extra matchings: cost in the millions (beyond r1/c06).
  Director's argument: for Z8 (flags 4ν, doubled matching 1/5, plain matching 2) or Z2×Z4, the class-2 pairs need
  ν(geodesic σ(p)→u) = ν(geodesic p→σ(u)) for almost all pairs, which forces ν to be a coboundary (killing the
  opposite-pair condition) unless σ is a polarity of the quadrangle (W(2^odd) only). So no W(13) 8-sheet lift.
- Bases with degree 15 + a doubled matching need a (15,4) graph > 5,632 vertices (record 5,070); Theorem-A bases give
  6·5,070 = 30,420 and 10·3,146 = 31,460. Below the floor.
- Route chart + a **plain fifth letter** (one extra controller colour carrying a single fibre map): 1.2M uncovered
  (beyond r2/d04), 63,770 uncovered at Z23 (beyond r4/f01). Do not repeat that design.
- Building / Weyl-distance graphs at max degree ≤ 17: nothing above 31,460 at D = 5 (beyond r1/c16; BEAT_16_5_SQUAD §1).
- Random Haar graphs at (17,5): about 19k vertices (size law). Plain random S will not do it.
- Deleting a 1-factor from the 18-regular (18,5) MDM graph (47,600): pairs with a unique route break; not promising.
- 5 letters × F4 = 20, 6 letters × F3 = 18, 9 letters × F2 = 18 charts were far below the MDM/route-chart values.
