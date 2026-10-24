# Independent re-check of BUILDINGS.md §1 (referee agent, 2026-10-24)

A separate agent refereed §1 of research/theorems/BUILDINGS.md. It wrote this code itself, without using the main
scripts in `..`. Run each script from this folder with python3 (numpy needed); the saved output is `review_out.txt`.

| script | checks |
|---|---|
| thin_check.py | Theorems 1 and 2 by BFS on thin buildings (Coxeter complexes): A₂–A₅, B₂–B₄, D₄, D₅, F₄, E₆, H₃, H₄, I₂(5, 7, 8, 9, 10, 12). It also shows that the first version of Theorem 2's "equivalently" line was off by one, and that the corrected line matches. |
| thick_check.py | Corollary 2 against BFS on PG(3,2), PG(4,2), Sp(6,2), O⁻(8,2), built from scratch |
| delorme_check.py | Theorem 3 on 300 random connected bipartite graphs (product diameter = D, quotient diameter ≤ D − 1) |
| asym_check.py | Theorem 4 constants in exact arithmetic at q ≈ 10⁶, 10⁷. Also the parameters of ²E₆(q): the weighted Poincaré sum over W(F₄) equals |²E₆(q)|/|B| for q = 2, 3, 4, 5, 7 |
| rates_check.py | the quoted 50 % / 90 % rows, the D = 12 comparison at q = 16, the B₃ quotient ratio, PG(4,3) and Sp(8,2) layers |

Verdict: "correct with fixable gaps". The gaps are listed and fixed in BUILDINGS.md §5, item 5.
