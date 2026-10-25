# Squad brief: round 4 — structured partial ovoids (q = 11 for (14,7), and the other D = 7 cells)

You are one card of an 8-card Haiku squad run by Opus (session cell-14-7, second session). Machine rules, scoreboard
and report format: as in research/squads/d14D7-r2/BRIEF.md ("Machine rules", "Report"; replace d14D7-r2 by d14D7-r4).
Read research/squads/d14D7-r3/BRIEF.md for the problem. Work only in research/squads/d14D7-r4/<card>/. No git.

## Where we are

Units per matching = size of a partial ovoid S of the elliptic section E of H(q)'s quadric (points of E pairwise
non-orthogonal); each point p of S gives a flag (p, spread line through p). Cell sizes: (14,7) = 1,771,560 + 4N (N at
q = 11; now 1,772,520 with N = 240, fully checked), (13,7) = 1,062,936 + 2N, (15,7) = 2,480,184 + 6N; (16,7) =
4,022,340 + 4N (q = 13, N = 252 now); (7,7) = 23,436 + 2N (q = 5, 48); (9,7) = 117,648 + 2N (q = 7, 84); (11,7) =
398,580 + 2N and (12,7) = 664,300 + 4N (q = 9, 138); (10,7) = 224,694 + 2N (q = 8, 52 by random packing).

What works best at q = 11: unions of ORBITS of an isometry of E. c3 (round 3): random order-4 isometry, orbit
compatibility graph (orbits whose points are pairwise non-orthogonal; two orbits compatible when all cross pairs are
non-orthogonal), clique search: 60 orbits x 4 = 240. An order-8 element also gives 240. Exact: the order-12 rotation of
the anisotropic plane A = (x0,x3) (identity on V4 = (x1,x2,x5,x6)) gives at most 17 orbits + 12 fixed points = 216
(secantclique.c). Plain local search on all of E stalls at 155-169.

## Files and tools (research/cell147/units/ unless noted; data in research/cell147/data/)

- E{5,7,11,13}.map: vertex i of E: hexagon point id, spread line id, coordinates x0..x6 (E is X4 = -C*X0 with C = 2, 1,
  1, 11 for q = 5, 7, 11, 13). coords{5,7,11,13}.txt, gh_{5,7,9,11,13}.txt (hexagons).
- perms_q11/*.txt: 23 permutations of the 15,984 vertices of E11 induced by isometries (c3's samples: orders 4, 8, 10).
- `orbitclique MAPFILE PERMFILE SECONDS SEED OUTFLAGS [INITFLAGS]` (q = 11 hard-wired: copy the source to your folder
  and change `static const int q` for other q): orbits = cycles of the permutation; weighted clique search. To use a
  GROUP (several generators), compute the orbits yourself and write a permutation whose cycles ARE the orbits (map each
  orbit's elements cyclically) — then orbitclique works unchanged.
- c3's sampler (Python/numpy): research/squads/d14D7-r3/c3/orth.py (random products of reflections in O(V), V =
  {x4 = -x0}, permutation of E's points; q = 11).
- secantclique.c, phaseils.c (A ⊥ V4 models), spreadpack.c (local search on E; INIT=flags to seed), pack (CHECKONLY
  scorer), t2cell.sh (cell builds), uhcheck, apsp_cyc. Current best flag files: sols/flags_q11_orbit4_240.txt,
  sols/flags_q11_orbit8_240.txt, sols/flags_q13_secant252.txt, sols/flags_q5_spread48.txt, sols/flags_q7_spread84.txt,
  sols/flags_q9_spread138.txt (GF(9), from research/squads/d14D7-r3/c6/spreadpack9.c).
- SCORER: `CHECKONLY=1 ./pack ../data/gh_Q.txt 0 1 /dev/null FLAGS` → "VALID N flags".
