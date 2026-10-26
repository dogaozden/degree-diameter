# referee omega-dq: tools

Written from scratch for the referee report `research/referee/omega-dq.md`. All C files compile with
`cc -O2 [-pthread] -o NAME NAME.c`. Python files take their inputs as arguments (run with `python3 -I`).

| file | what |
|---|---|
| `hexgen.c` | H(q), q prime, split-octonion model, loop over point pairs: `./hexgen 7 h7.txt` |
| `hexgf.c` | H(q), any prime power q <= 16, same model, lines via the kernel of y -> xy: `./hexgf 9 h9.txt` |
| `bitapsp.c` | all-pairs BFS (64 sources per pass, no symmetry): degrees, bipartite, diameter, girth: `./bitapsp h7.txt 4` |
| `omegaref.c` | Omega H_q from Figs 2.21a/b in memory, reading 1 or 2, any block pattern, sigma `id` or `rand:SEED`; BFS reports with witness and Theorem 1/2 bookkeeping: `./omegaref h7.txt 7 ababa 2 id src -1 -2` (also `reps`, `sample N SEED`, `kall`) |
| `omegacheck.py` | second Omega H_q build (reading 2) and BFS in Python: `python3 -I omegacheck.py h7.txt ababa 0 0 0 0 57` |
| `omegalab.py` | Omega B_1 with a labelling per copy (or the same labelling everywhere), edge list for `bitapsp`: `python3 -I omegalab.py hex TYPES INNER LAB out` |
| `thm2_bound.py` | Theorem 2's counting bound for q = 2..16 |

Reproduce the q = 7 witness (about 1 s, 0.2 GB):

    cc -O2 -o hexgf hexgf.c && ./hexgf 7 h7.txt
    cc -O2 -pthread -o bitapsp bitapsp.c && ./bitapsp h7.txt 4        # diameter 6, girth 12
    cc -O2 -o omegaref omegaref.c && ./omegaref h7.txt 7 ababa 2 id src -1
    # -> source 980400 = K(t=0, k=0): eccentricity 9 ... witness: d(980400, 57) = 9, point 57 of copy 0

The q = 9 case: `./hexgf 9 h9.txt && ./omegaref h9.txt 9 aaabbb 2 id reps` (about 10 s, 0.6 GB). q = 13 needs about 5 GB.

Logs: `logs/hex_checks.txt`, `logs/omega_q7.txt`, `logs/omega_q8_q9_q11_q13.txt`, `logs/omega_q3_q5_allpairs.txt`,
`logs/audit_relabelled_q3.txt`, `logs/thm2_bound.txt`.
