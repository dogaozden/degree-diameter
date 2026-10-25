# optimal-sat handoff

Read `SUMMARY.md` first (what is proved), then this file (what is open and how to continue).

## Done (2026-10-25)

1. **Upper bounds from published theorems that the wiki table lacks:** N^b(15,3) ≤ 418 (wiki 422) and
   N^b(7,5) ≤ 3104 (wiki 3106). SUMMARY.md §0.
2. **Theorem Q** (new): a bipartite (k,3,−2)-graph is the same as an oriented (k−2)-regular graph A on C(k,2)
   vertices with (2I+A)(2I+A)ᵀ = kI + 2J, plus a weighing-matrix signing W of A (WWᵀ = (k−2)I). Full proof:
   `defect2/PROOF.md`. It recovers the known "k or k−2 is a square" condition.
3. **Certified computations** (DRAT, drat-trim VERIFIED): no (k,3,−2)-graph for k = 5..9; for k = 10 not even the
   oriented graph A exists. Logs: `logs/cert/`. (Δ = 6, 9 had only hand proofs before.)
4. **k = 9 structure:** A exists (a 3-class scheme built on the Fano plane), but no signing; a 13-square "sphere"
   certifies it. `defect2/NOTES.md`.
5. Squad r1 on (k,3,−4) (`research/squads/r1-defect4/`, LOG.md): reproduced k = 6 UNSAT in 127 s; nobody reached
   k = 7. Defect 4 has long repeat cycles, so there is no small quotient.

## Open: k = 11 (the (11,3) cell; UNSAT would give N^b(11,3) ≤ 218)

- Monolithic A-only runs ran about 7 CPU-hours (kissat) and 5 CPU-hours (CaDiCaL + streamed LRAT check) without an
  answer; they die with this session.
- Case split ready for a cluster (rule R1 = "vertex 0 lies on the most directed triangles", 245,667 degree-sequence
  cubes):
  - `bash defect2/setup_worker.sh ~/w`
  - `bash defect2/worker.sh ~/w i n 4` (certified per cube by streamed LRAT).
  - Request with the recipe: `research/squads/requests/2026-10-25T0915-optimal-sat-k11-cubes.md`.
  - Done under R1, certified: the t = 0, 1, 2 cubes (and the t ≤ 3 cubes listed in `logs/k11_lowt.log`).
- Costs: most cubes take seconds; low-t, flat-α cubes take minutes to hours (`logs/defect2_calibration.md`).
  Rule R2 (base arc on the most triangles) speeds up some hard cubes a lot (20+ min → 3 s) but not all. It needs its
  own cube list (`ablist.py --maxtau`), and the two rules must not be mixed.
- If a cube is SAT: decode A from the model and run `defect2/signs_gf2.py` (GF(2) elimination decides the signing;
  `cegar.py` loops). A signable A would give a 220-vertex (11,3) graph, which is optimal.

## Tools

Solvers are not in the repo:
- `git clone https://github.com/arminbiere/kissat` (and `cadical`), then `./configure && make`;
- `git clone https://github.com/marijnheule/drat-trim`, then `make` and `gcc -O2 -o lrat-check lrat-check.c`;
- `pip install python-sat`.

`defect2/`:
- `enc_quot.py` (main encoder), `PROOF.md` (why it is sound);
- `certify.sh` (DRAT), `stream_cert.sh` / `run_cube.sh` / `run_abcube.sh` (streamed LRAT);
- `cube_list.py` + `cover_check.py` (B-row split with a drat-trim cover check), `ablist.py` + `abcube.py`
  (degree-sequence split);
- `subcase.py`, `tmax.py`, `tausplit.py` (experiments).
