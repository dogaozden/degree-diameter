# optimal-sat handoff

Read `SUMMARY.md` first (what is proved), then this file (what is running and what to do next).

## State (2026-10-25, about 09:20 UTC)

- Main target: **no bipartite (11,3,−2)-graph**, which would give N^b(11,3) ≤ 218 (wiki: 220). By Theorem Q
  (SUMMARY.md §1) this is the same as: no oriented 9-regular graph A on 55 vertices with
  (2I+A)(2I+A)ᵀ = (2I+A)ᵀ(2I+A) = 11I + 2J together with a ±1 signing W of A with WWᵀ = 9I.
  The A-only instance alone would suffice (if it is UNSAT).
- Done and certified: k = 5..9 (A + signs) and k = 10 (A only), DRAT-verified (logs in `logs/cert/`).
- k = 11 is **open in this session**:
  - kissat on the A-only instance (`enc_quot.py 11 --sym --nf2 --ntt --alltr`, sha256 b6101044…) has had about 2.6 CPU-hours.
  - CaDiCaL on the same CNF streams an LRAT proof into lrat-check (`stream_cert.sh`, about 1.8 CPU-hours so far).
  - kissat on the signed instance (`--signs --sym --nf2 --ntt --alltr`) has just started.
  - A sequential certified cube runner (`run_cube.sh` over `cube_list.py 11 2`, 110 cubes) is in the scratchpad.
  - Two sample cubes needed more than 15 CPU-minutes each (machine oversubscribed).
- Compute request for the coordinator: `research/squads/requests/2026-10-25T0915-optimal-sat-k11-cubes.md`
  (110 independent certified cube jobs + a cover check).
- Solvers are not in the repo. Build: `git clone https://github.com/arminbiere/kissat && cd kissat && ./configure && make`,
  same for `cadical`; `git clone https://github.com/marijnheule/drat-trim && make` and
  `gcc -O2 -o lrat-check lrat-check.c`. `pip install python-sat`.

## Results so far

| k | A only | A + signs |
|---|---|---|
| 3, 4 | SAT | SAT (the known graphs) |
| 5–8 | UNSAT (< 1 s) | UNSAT, DRAT verified |
| 9 | SAT (1.6 s): a 3-class non-symmetric scheme built on the Fano plane | UNSAT (3.6 s), DRAT verified |
| 10 | UNSAT (163–216 s), DRAT verified | — |
| 11 | running (> 2.5 CPU-hours) | running |

What did not help (see `logs/defect2_calibration.md`): RoundingSat, march_cu cubing, the kissat `--unsat` preset,
and Cayley or semiregular symmetric searches (no Cayley digraph on either group of order 55; order-11 and order-5
automorphisms not decided in 900 s).

## Decompositions tried for k = 11 (details in defect2/NOTES.md items 10-12 and logs/defect2_calibration.md)

- 2 rows of B (`cube_list.py`, 110 cubes): sample cubes > 15 CPU-minutes.
- Degree sequences of B (`ablist.py`, 245,667 cubes after reversal symmetry): 16 of 20 random cubes take about
  1 s, a few take minutes, some more than 5–20 minutes. The hard ones have few directed triangles at vertex 0
  (small t, flat α).
- "Vertex 0 has the most directed triangles" (valid choice, `abcube.py --maxt`, `tmax.py`): t = 0 cube UNSAT in
  53 s (certified, 55 s), t = 1 cube 106 s; "every vertex on ≤ 2 (resp. 5) triangles" not finished in 10 (40) min.
- Turnkey cluster workers: `defect2/setup_worker.sh`, `defect2/worker.sh` (see the compute request).

## Next steps

1. Finish k = 11: monolithic runs, or the 110 cubes (`run_cube.sh`, each certified by streamed LRAT), then
   `cover_check.py`. If any cube is SAT, run `signs_gf2.py` on the model (CEGAR: `cegar.py`).
2. If UNSAT: write it into SUMMARY.md as "N^b(11,3) ≤ 218" with the hashes and logs; the coordinator re-checks.
3. Secondary (not promising this session): (k,3,−4) — squad r1 reproduced k = 6 UNSAT in 127 s (card c1) but nobody
   reached k = 7; the table needs k = 11 and 15. D = 5 defect 6: structure noted (girth 8, three repeats per vertex),
   no method yet.
