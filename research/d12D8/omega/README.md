# research/d12D8/omega: Gómez's ΩH_q rebuilt and checked (job own-12-8, 2026-10-26)

Verdict and proofs: `research/squads/cells/d12D8_table.md`. Large files (hexagons, edge lists, generators) are not
committed; every one is rebuilt by the commands below.

| file | what |
|---|---|
| hexq6.c | H(q) in Q(6,q) with Tits' equations, q prime, 4, 8, 9: lines and point coordinates (`hexq6 q hex_q{q}.txt`) |
| hexedges.py | incidence graph edge list of a hexagon file (for apsp_mt) |
| hex_checks.txt | apsp_mt on H(q), q = 3, 4, 5, 7, 8, 9, 11, 13: bipartite, (q+1)-regular, diameter 6 (⇒ girth 12) |
| omega.c | edge list of ΩB₁ for B₁ = H(q): `omega HEX TYPES READING OUT [SIGMA]` (reading 1 = thesis drawing convention, 2 = Oct 25 reading) |
| omega_bfs.c | the same graph without an edge file; degree check + BFS from one vertex (used up to 36M vertices) |
| haut.py | automorphisms of H(q) from SL(3,q) ≤ G₂(q) (Singer cycle, transvection), each checked to map lines to lines |
| sigma.py | pairings σ (points → lines) for reading 1: identity, random, Singer-equivariant |
| omgens.py | generator permutations of ΩH_q (rotation, block swaps, hexagon automorphisms) for apsp_auto |
| apsp_auto.c | apsp_mt + symmetry: checks each generator edge by edge, BFS from one vertex per orbit, witness pair |
| bfs1.c | plain one-source BFS with distance counts and d(s,t) (independent re-check of witnesses) |
| twist.py | ΩH_q with randomly relabelled copies (repair test) |
| check_om9_r2.txt, check_om9_r1s.txt | apsp_auto logs: exact diameter 9 for ΩH₉, readings 2 and 1 |
| thesis_values_bfs.txt | omega_bfs from a K₁-vertex for q = 5, 7, 8, 11, 13: eccentricity 9 |
| witness_pairs.txt | pairs at distance 9 in ΩH₉ (both readings) with re-check commands |
| sig_q*_singer.txt | the Singer-equivariant pairings used |

Build: `cc -O2 -o hexq6 hexq6.c`, `cc -O2 -o omega omega.c`, `cc -O2 -o omega_bfs omega_bfs.c`, `cc -O2 -o bfs1 bfs1.c`,
`cc -O2 -pthread -o apsp_auto apsp_auto.c`; apsp_mt is research/lifts/coordinator_check/apsp_mt.c.

Main commands (q = 9; ~1 min each, ≤ 2 GB):
```
./hexq6 9 hex_q9.txt
./omega hex_q9.txt aaabbb 2 om9_r2.txt
python3 haut.py hex_q9.txt haut_q9.npy singer trans
python3 omgens.py hex_q9.txt aaabbb 2 haut_q9.npy g9_r2.bin
./apsp_auto om9_r2.txt g9_r2.bin 12 8 4          # 18 orbits, diameter 9
python3 sigma.py hex_q9.txt singer sig_q9_singer.txt haut_q9.npy
./omega hex_q9.txt aaabbb 1 om9_r1s.txt sig_q9_singer.txt
python3 omgens.py hex_q9.txt aaabbb 1 haut_q9.npy g9_r1s.bin sig_q9_singer.txt
./apsp_auto om9_r1s.txt g9_r1s.bin 12 8 4        # 4,380 orbits, diameter 9
./bfs1 om9_r2.txt 3986710 0                      # d = 9
./omega_bfs hex_q13.txt aaaabbbb 2 32178720      # ΩH_13, 36,201,060 vertices: eccentricity 9
```
