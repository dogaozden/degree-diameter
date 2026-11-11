# c8 (wildcard): 2+2 voltage lifts of metacyclic groups, n = 4N >= 4972

Idea: two vertex orbits per side (base multigraph [[a,4-a],[4-a,a]], a = 1 or 2), voltage group G = Z_m x|_r Z_k,
N = |G| = 1243..1300. Vertices A_{i,g}, B_{j,h}; A_{i,g} ~ B_{j,g s} for s in S_ij. Normalised: 1 in S_00, S_01, S_10.
Left translation is an automorphism, so diameter <= 9 iff BFS from the 4 orbit representatives reaches all within 9.
cost = sum over the 4 representatives of #vertices at distance > 9. cost 0 iff diameter <= 9. Not a Haar graph.

Files: lift22.c (evaluator + annealing/ILS), mkgroups.py (metacyclic groups of order N, deduplicated),
groups_all.txt (N 1243..1262), groups_ext.txt (N 1263..1300), nonab_sorted.txt, screen1.txt, screen2.txt (filtered lists),
found/ (edge lists of the best states: dump_m139_k9_r42_a2.edges is cost 12, n = 5004).

Build and run (each command under 100 s):
  gcc -O3 -march=native -o lift22 lift22.c -lm
  ILS=1 ./lift22 screen1.txt 9 9 45 92 found      (line 9 = Z_139 x| Z_9, r = 42; prints RES lines, DUMP with DUMP=1)
  (without ILS=1: simulated annealing, 20000-step epochs). SCANLIM env var sets the per-coordinate scan limit for ILS.

Results (best cost; lower is better; all heuristic, not exhaustive):
- Abelian groups are hopeless: Z_1243 cyclic, 2+2 lift: cost 3834 (40 s SA).
- Dihedral D_623 (N = 1246), D_625 .. : 6760 to 9518 (8 s).
- Z_139 x| Z_9 (r = 42), N = 1251, n = 5004: cost 12 (a = 2) in 4 of 6 ILS runs of 45 s; a = 1: 12-20.
  Validated: dump has score48 far pairs 7506 = N*12/2 exactly (diameter 10). Far vertices are at distance exactly 10.
- Z_251 x| Z_5 (r = 20), N = 1255, n = 5020: 16 (SA 40 s), 18 (ILS 45 s).
- Z_422 x| Z_3 (r = 225), N = 1266: 22 (SA 4.5 s), 24 (ILS 45 s).
- Z_209 x| Z_6 (r = 87), N = 1254: 25 (ILS 45 s). Z_105 x| Z_12 (r = 17), N = 1260: 27 (ILS 45 s).
- N = 1248 (Z_208 x| Z_6 r = 159: 25; Z_208 x| Z_6 r = 55: 30; Z_312 x| Z_4 r = 83: 35), Z_215 x| Z_6 (N = 1290): 34 (10 s ILS).
- Other screened groups (5 s SA) were 30 to 400.
No cost-0 lift found in the screened families. Floor for the best group is about 12 (not zero).

Next (not done): exhaustive scan of the 5 free voltages of Z_139 x| Z_9 modulo Aut(G) is about 1e10 evaluations (too many
for this slot); 3+3 base lifts (N >= 829) would give more freedom; targeted moves (pick an uncovered vertex, reroute one voltage).
