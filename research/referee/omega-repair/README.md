# referee-omega-repair: tools and logs

Report: `research/referee/omega-repair.md`. Everything here is new code. It does not use the code under review
(`research/omega_repair/` on branch claude/thm-omega-repair-m4luls), except in the §5.4 check, which runs that note's
saved q = 3 twist file on the hexagon its own `hexq6.c` writes.

## Commands (run in this folder)

    python3 octo.py                                   # the octonion product composes norms (q = 3, 4, 5, 7, 8, 9)
    for q in 3 7 8 9; do python3 buildhex.py $q; done # H(q) -> hex_qQ.txt, hex_qQ.npz (q = 9: about 10 minutes)
    gcc -O2 -march=native -o ghcheck ghcheck.c && for q in 3 7 8 9; do ./ghcheck hex_q$q.txt; done
    for q in 3 7 8 9; do python3 collin.py $q; done   # generators are collineations
    python3 drg.py                                    # Lemma 3.1 from the intersection array
    python3 mytypes.py 7 140                          # Lemma 4.3: types, Bonferroni bounds, forced pairs
    python3 e2e43.py 3 2500                           # Lemmas 4.1, 4.3 on explicit configurations in Q(6,7)
    python3 myperp44.py 400 11                        # Lemma 4.4 sampling at q = 7
    for p in aaaaa aaaab aaabb aabbb abbbb bbbbb; do python3 myroutes.py 7 $p; done   # q = 7 starved pairs
    python3 sweep.py 8 5; python3 sweep.py 9 6; python3 sweep.py 11 7; python3 sweep.py 13 8   # Computer-checked 3.4
    python3 totals.py 8 5; python3 totals.py 9 6      # total far-pair lower bounds
    python3 perclass.py 8 aabbb; python3 perclass.py 13 aaaabbbb   # per-(class, copy) labellings: counting fails
    gcc -O2 -march=native -o omg omg.c && gcc -O2 -march=native -o omg_all omg_all.c
    python3 driver.py 8 aabbb 1 b0 13 0               # q pattern seed class copy row  (see below)

`driver.py q pattern seed class copy row`: builds ΩH_q (reading 2) with P_c = a_c, L_c = b_c for random collineations,
runs `omg` (BFS from hub (row, class); class `u0`..`u4` unbarred, `b0`..`b4` barred), and compares the reached
target-colour vertices of `copy` with the union of route balls from `myroutes.py`. Seed −1 is the thesis labelling.
Seeds −2 and −3 use one random collineation per copy (a_c = b_c), the case of Lemma 1.2.

§5.4 (the note's annealed q = 3 file), with `NOTE=` the note's `research/omega_repair`:

    mkdir -p theirs && cc -O2 -o theirs/hexq6 $NOTE/hexq6.c && ./theirs/hexq6 3 theirs/hex_q3_theirs.txt
    python3 convert_theirs.py theirs/hex_q3_theirs.txt $NOTE/twists/q3_aba_annealed.bin theirs/hex3.txt theirs/lab_q3_ann.bin
    ./ghcheck theirs/hex3.txt && ./omg_all theirs/hex3.txt theirs/lab_q3_ann.bin aba && ./omg_all theirs/hex3.txt theirs/lab_q3_ann.bin aba A

In mode `A`, `omg_all` runs BFS from every vertex, so each far pair is counted once from each end.

## Logs

| log | what |
|---|---|
| `lemma31_drg.txt` | \|B(z,R) ∩ opp(t)\| for every q, radius and distance |
| `lemma43_types.txt` | the 17 types at q = 7, m₂ = 140 |
| `lemma41_43_configs_q7.txt` | Lemma 4.1 overlap values; 2,500 configurations against their type bounds |
| `lemma44_sampling_q7.txt` | d_c, \|Perp(h)\| for 224 fixed-point-free collineations; ⊥ ⟺ distance ≤ 4 |
| `routes_q7_starved.txt` | starved pairs and m₂ per bar, q = 7 |
| `sweep_q8.txt` … `sweep_q13.txt` | best pair per pattern, worst pattern (Computer-checked 3.4) |
| `total_far_bounds_q8_q9.txt` | lower bounds on all far pairs |
| `perclass.txt` | per-(class, copy) model: radius-4 / radius-2 centre counts |
| `ghcheck.txt`, `collineation_generators.txt` | the hexagons and the generators |
| `bfs_q7.txt`, `bfs_q8.txt`, `bfs_q9.txt` | explicit ΩH_q at the thesis orders: BFS from hubs, predicted = reached |
| `their_annealed_q3.txt` | the note's annealed q = 3 labelling: 259,169 far pairs, diameter 9 |
