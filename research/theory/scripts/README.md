# theory/scripts

Run from this folder with python3 (numpy only). Total running time: about 10 minutes, most of it `sim2.py`.

- `groups_inv.py`: centre size, involution counts and |G'| for the record groups. Formulas for SL, PSL and PGL(2,q)
  are brute-force checked by `python3 groups_inv.py`.
- `model.py`: the Poisson model of THRESHOLD.md §3. It combines special targets for odd D with the first-order
  coincidence losses.
- `data_check.py`: reads `../../frontier/sols` and `../../d5/sols`. Prints the per-cell table, the per-D table and
  the μ fits. Output: `data_check_out.txt`.
- `data_check2.py`: Theorem 2 check, budget ("best of T") model and parity × family table. Output:
  `data_check2_out.txt`.
- `budget_loo.py`: leave-one-out for the budget model. Output: `budget_loo_out.txt`.
- `sim.py [trials]`: Monte Carlo at n = 1320 with multiplication tables. Output: `sim_out.txt`, `sim_results.csv`.
- `sim2.py [trials]`: Monte Carlo for SL and PSL(2,p) up to n = 68,880. Output: `sim2_out.txt`,
  `sim2_results.csv`.
