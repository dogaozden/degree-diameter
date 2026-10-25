# Scripts behind `research/referee/haar-2026-10-25.md`

Written by the referee from scratch. None of them shares code with the lab's checkers. Run each from this folder with
`python3`; they read the solution files from `research/frontier/sols/` by absolute path
(`/home/user/degree-diameter/...`). Edit that prefix if the repository lives elsewhere.

| script | what it checks | output |
|---|---|---|
| `refcheck.py FILE...` | Haar graph H(G, S), with G = Q₁ [× Q₂] × Z_n and Qᵢ = SL/PSL(2,q). It uses its own GF(q) tables, built from the header polynomial, and its own SL/PSL enumeration. It runs BFS from (e,A) and (e,B) (Cor. 2.3 of the note), and checks that the generators are distinct and that each left multiplication is a bijection. | `refcheck_batch.out`, `refcheck_batch2.out`, `refcheck_small_and_new98.out` |
| `refcheck.py neg_78_*.txt` | negative controls: the (7,8) file with D = 7, and with s_1's z changed from 6 to 7 | `negative_controls.out` |
| `metacheck.py` | the four metacyclic records, plus the newer (5,9) graph on master | `metacheck.out` |
| `s0check.py` | each f = 0 file: solves α(s₀)s₀⁻¹ = τ, then checks α(T s₀) = T s₀ and the cycle sizes (α, τ from the note's `orbit_check*.log`) | `s0check.out` |
| `lift38_profiles.py` | rebuilds the (3,8) lift and compares BFS distance profiles within each colour class | `lift38_profiles.out` |
| `abound_check.py` | recomputes A(Δ, D) for Δ = 3..16, D = 8..10, and tests the parity-class polynomial remark | `abound_check.out` |
| `table_numbers.py` | recomputes 2\|G\|, gains and Moore-bound fractions for the 34 rows | `table_numbers.out` |
