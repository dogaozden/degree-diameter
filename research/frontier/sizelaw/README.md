# sizelaw: scripts behind ../SIZE_LAW.md

Run them from this folder; the Python scripts read `../sols`, `../../d5/sols` and `~/AI_Projects/research-lab/records.json`.
- `data.py`: W(Δ,D), N_h, μ = N e^(−W/N), solution-file reader, wall list.
- `fit.py`: the §1 fits; writes `size_law_fits.csv`. `predict.py`: the μ\*-law fit, leave-one-out and per-cell
  predictions (`pred.json`). `table_md.py`: the §3.3 markdown table. `csv_extra.py`: the full CSV with runs and
  predictions (it reads `big/*.log`).
- `cands.py`: candidate groups (SL/PSL(2,q) × Z_n, SL × SL × Z_n) in an order window.
- `zbal.py`: Z_n fiber loads (§2.3.3).
- `haar_orb.c`: haar_gen3 plus ORBIT mode (symmetric S), DUMPUNC, LEVELS and the RANDSAMPLE mean/variance.
  Build: `cc -O3 -o haar_orb haar_orb.c -lm`.
- `haarcheck_sl.c`: independent low-memory checker for SL(2,p) × Z_n, p prime. Build: `cc -O3 -o haarcheck_sl haarcheck_sl.c`.
- `cap_run1.sh`, `cap_jobs.txt`: the (7,8) capability experiment (§4.1).
