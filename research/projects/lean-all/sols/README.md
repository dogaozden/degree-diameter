# Sol files written by lean-all

- `d7D10_prod_psl_19_sl_7_1_swapped.txt`: `research/frontier/sols/d7D10_prod_sl_7_psl_19_1_orb3_s2.txt` with the two
  matrix factors swapped (`swap_sol.py`); the same Haar graph up to isomorphism.
- `d8D10_prod_psl_19_psl_7_7_swapped.txt`: `research/frontier/sols/d8D10_prod_psl_7_psl_19_7_orb3_s1.txt`, factors
  swapped.
- `d15D7_hub_10826_10481.txt`: a hub graph for the (15,7) cell (`research/frontier/sols/d15D7_hex11_typedrelax2_n2501491.sol`),
  lines `b a` with `b < 10826` (line-side hubs) and `a < 10481` (point-side hubs), 83,848 edges, degrees at most 8.
  Same-side distances are at most 6 in the hub graph alone (the record's own hub graph needs the levels for 1,403
  pairs). Made from the record's hub graph by 3,344 degree-preserving edge swaps aimed at far pairs
  (research/projects/lean-all/tools/opt.c; far.c counts far pairs); checked by a bit-set BFS from every vertex and by plain BFS from 300 sampled sources.
  sha256 819c113443bd80e0100baa2f0f57896c492136ac9a50d6da3adf0dd0d65bbc1f.
- `d12D7_aux_gens.json`: automorphism generators (nauty, through `auts.py`) of the auxiliary graph of the (12,7) cell
  (`gen_spreadhub.py --write-aux`: hubs, owners, spread lines and their dual images); the cell checks them in Lean.
