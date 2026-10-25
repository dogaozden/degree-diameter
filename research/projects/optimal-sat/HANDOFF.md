# optimal-sat handoff

Read `SUMMARY.md` first (what is proved), then this file (what is running and what to do next).

## State (2026-10-25)

- Main target: **no bipartite (11,3,−2)-graph**, which would give N^b(11,3) ≤ 218 (wiki: 220). By Theorem Q
  (SUMMARY.md §1) this is the same as: no oriented 9-regular graph A on 55 vertices with
  (2I+A)(2I+A)ᵀ = (2I+A)ᵀ(2I+A) = 11I + 2J together with a ±1 signing W of A with WWᵀ = 9I.
- Encoder: `defect2/enc_quot.py 11 out.cnf [--signs] --sym --nf2`. `--nf2` uses Lemma Q2 (vertex 0, its out-set
  O = 1..9, in-set I = 10..18, R = 19..54 labelled by the pairs of O, all arcs R→O fixed). `--sym` adds lex-leader
  clauses for adjacent transpositions of O (acting on R through the pair labels) and of I.
- Certified runs: `defect2/certify.sh k "<opts>" outdir` (kissat + binary DRAT + drat-trim). Done for
  k = 5..9 with signs (all VERIFIED), k = 10 A-only in progress.
- Solvers are not in the repo. Build: `git clone https://github.com/arminbiere/kissat && cd kissat && ./configure && make`,
  same for `cadical`; `git clone https://github.com/marijnheule/drat-trim && make`. `pip install python-sat`.

## Results so far

| k | A only | A + signs |
|---|---|---|
| 3, 4 | SAT | SAT (the known graphs) |
| 5–8 | UNSAT (< 1 s) | UNSAT, DRAT verified |
| 9 | SAT (1.7 s): A is a 3-class non-symmetric scheme, A² = 4Aᵀ + (J−I−A−Aᵀ) | UNSAT (3.6 s), DRAT verified |
| 10 | UNSAT (211 s) | — |
| 11 | running | running |

## Next steps if k = 11 does not finish

1. Cube-and-conquer on the O→I arcs (81 variables; double-lex symmetry already applies to that 9×9 block).
2. Stronger symmetry breaking: all transpositions of O and I, not only adjacent ones.
3. Use Lemma Q2 at more vertices (it holds at every vertex) to add implied constraints.
4. Spectral facts (SUMMARY.md): eigenvalues of A other than 9 lie on |λ+2| = √11; A cannot be a 3-class scheme
   like the k = 9 one.

## Secondary targets (not started)

- (15,3,−4): excluding it gives N^b(15,3) ≤ 416.
- D = 5 defect 6, e.g. (4,5,−6) (gives N^b(4,5) ≤ 234): the graph has girth 8 and every vertex has exactly
  three repeats at distance 4.
