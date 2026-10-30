# research/sage: SageMath builders for the lab's record graphs

One `.sage` file per construction. Each file has a function such as `build_d3_four_hats(q)` that returns a Sage
`Graph`, and ends with `check(q)`, which prints the number of vertices, the maximum degree, `G.is_bipartite()` and
`G.diameter()` next to the expected values. Running a file with `sage FILE.sage` runs its checks at the smallest
parameters; to only load the functions, set `NO_AUTO_CHECK = True` first.

Every file was run in a real Sage (passagemath 10.8.13); the output is in `RESULTS.md` and `logs/`.

## Which file builds which record

| Diameter | Record or family | File | Function | Source in the repo |
|---|---|---|---|---|
| 3 | four hats (+2 over Araujo-Pardo and López), PG(2,q), q ≥ 4; also their three hats | `d3_four_hats.sage` | `build_d3_four_hats(q)`, `build_d3_three_hats(q)` | `research/plus2/coords/coords-standalone.tex`, `SYNTHETIC.md` §1 |
| 3 | (16,3) on 396 vertices: PG(2,13) and three four-hat gadgets on one Singer orbit | `d3_16_three_gadgets.sage` | `build_d3_16_three_gadgets()` | `research/d3d6/` (`REPORT.md`, `multi_gadget.py`, `graphs/sym3_q13_*.json`) |
| 4 | Theorem A: the Ahrens-Szekeres quadrangle AS(q) with clones of two elliptic quadrics, q odd, 2q²(q+2) vertices | `d4_theoremA_ASq.sage` | `build_d4_ASq(q)` | `SYNTHETIC.md` §2.3, `research/gq4x/` |
| 4 | Proposition C: a 2-ovoid and a spread of W(q) in the Singer (cyclic) model, q odd prime, 2(q²+1)(q+3) vertices | `d4_propC_Wq.sage` | `build_d4_propC(q)` | `SYNTHETIC.md` §2.4, `research/synthetic/checks/check_d4.py` |
| 4 | the (7,4) example on 359 vertices: Q(4,5), clones of an ovoid, 21 shadow lines | `d4_7_4_359_Q45.sage` | `build_d4_7_4_359()` | `SYNTHETIC.md` §2.6, `research/synthetic/checks/q4_359_lines.json` |
| 5 | (7,5) on 1,200 vertices: Haar graph of SL(2,5) × C5 | `d5_haar_7_5_1200.sage` | `build_d5_haar_7_5_1200()` | `research/beyond-haar-d5/records/d7D5_n1200_haar_sl5xc5.txt` |
| 5 | (5,5) on 360 vertices: lift of [[2,3],[3,2]] by C15 × S3 | `d5_lift_5_5_360.sage` | `build_d5_lift_5_5_360()` | `research/beyond-haar-d5/records/` |
| 5 | (5,5) on 384 vertices: lifts of 4-vertex bases by groups of order 96 (the Lean-checked record is `a1_g96_31`) | `d5_lift_5_5_384.sage` | `build_d5_lift_5_5_384(variant)` | `research/beyond-haar-d5b/records/` |
| 5 | helper used by all Haar and lift records: `haar_graph(G, S)` and `voltage_lift(...)` | `haar.sage` | `haar_graph`, `voltage_lift` | `research/frontier/build_haar2.py` |
| 6 | Theorem D: the split Cayley hexagon H(q), a Hermitian spread, whiskers, doubling with levels; also the regular version (Theorem R) | `d6_theoremD_hexagon_doubling.sage` | `build_d6_theoremD(q, m)`, `build_d6_theoremR(q, m)` | `SYNTHETIC.md` §3, `research/synthetic/checks/check_d6.py` |
| 6, 7, 8 | the split Cayley hexagon H(q) and its Hermitian spread (helper) | `hexagon.sage` | `hexagon(q)` | `research/synthetic/checks/check_d6.py` |
| 7 | copies of H(q) or of its dual joined by matchings, freed sets and hubs (general builder) | `d7_hexagon_copies_hubs.sage` | see the file header | `SYNTHETIC.md` §4, `research/synthetic/conics2/typed_build.py` |
| 8 | Gómez's Ω H_q on 5α copies of H(q) with our labelling | `d8_gomez_omegaH.sage` | see the file header | `SYNTHETIC.md` §6, `research/synthetic/checks/check_d8.py` |

`compare/compare_dN.sage` compares each family with the lab's Python builder at the same parameters, by exact
edge-set equality after relabelling where the Python builder numbers things the same way, and by `is_isomorphic`
otherwise. `run_all.sh` runs everything and refreshes `logs/`.

## Labels

A vertex label is the geometric object. The first entry is 0 for the point side and 1 for the line side.

* PG(2,q): `(0, x, y, z)` is the point (x:y:z), `(1, u, v, w)` the line [u:v:w], first non-zero coordinate 1; the point is on
  the line when ux + vy + wz = 0. New vertices: `(0,'Q')`, `(0,'H',s)`, `(1,'M')`, `(1,'K',s)` (D = 3, as in the papers).
* AS(q): `(0, a, b, c)` is the point (a, (b, c)); `(1,'A',p2,p3,a,b,c)` is a coset line and `(1,'B',b,c)` a fibre; clones are
  `(0,'clone',...)`.
* Q(4,q), W(q), H(q): points are normalised coordinates in the ambient projective space; a line is `(1, ...)` followed by the
  reduced row echelon form of the matrix of two of its points.
* Haar graphs and lifts: `(0, g)` and `(1, g)` with `g` a group element; `(0, 'A0', g)`, `(1, 'B0', g)` for the vertices of a lift.

## How to run

```
cd research/sage
sage d3_four_hats.sage                    # runs check(4) and check(5)
sage -c 'NO_AUTO_CHECK = True; load("d3_four_hats.sage"); G = build_d3_four_hats(7); print(G.diameter())'
sage compare/compare_d3.sage              # compare with the Python builder
SAGE=sage ./run_all.sh                    # everything
```

Run from this directory: several files `load` `haar.sage` or `hexagon.sage`, and the comparison scripts find the repo
by going two levels up. The comparison scripts import the lab's Python code (they need `networkx` and `numpy`, which
Sage has).

## Getting Sage

What worked here (Python 3.13, a fresh virtual environment, about 10 minutes): `python3 -m venv v; v/bin/pip install passagemath-standard`.
That gives `v/bin/sage` (passagemath 10.8.13). It includes GAP with the small groups library, which
`d5_lift_5_5_384.sage` needs (`libgap.SmallGroup(96, 31)`). The other two routes listed in the brief were not needed.
