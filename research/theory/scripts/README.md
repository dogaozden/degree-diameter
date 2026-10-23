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

## BEYOND_RANDOM.md (second session)

- `orbit_model.py`: the clumped Poisson mean μ_A of α-invariant S (formula (1)), with the fixed-point structure of
  conjugation of order 3 on SL/PSL/PGL(2,q) × Z_n.
- `beyond_predict.py`: every orbit run's μ and μ_A, the effort-law test and the per-cell gain predictions P0, P1 and P3.
  Output: `beyond_predict_out.txt`. Data: `orb_runs.txt`, `cmp_runs.txt` (from the structured job's logs).
- `symgroups.py`: exact Q × Z_n arithmetic (SL/PSL(2,p^e)), conjugation and Frobenius automorphisms.
- `collisions.py FAM p e n d L samples MODE...`: distinct word values and coinciding-pair patterns for random,
  conjugation-, Frobenius- and order-2-symmetric S. Outputs: `coll_*.txt`.
- `symmetry_options.py`: μ_A for each candidate symmetry and group per cell, plus the reach table at 4 core-hours.
  Output: `symmetry_options_out.txt` (a few seconds).
- `exp/`: haar_sym screening and anneal runs (commands in `exp/README.md`).
