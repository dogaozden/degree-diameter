#!/usr/bin/env python3
"""c10: baselines for LPS x Z_m covers (random equivariant, random free, exhaustive equivariant t2 search).

Grids: p=5 q in {13,17,19,23,29}; p=7 q in {11,13,17,19,23}; m prime, m = 1 mod 3, m <= 61; q(q^2-1)m <= 1e7.
Excess = diam - log_p(q(q^2-1)m/2), FULL cells only (compA == q(q^2-1)m and compB == q(q^2-1)m as printed by haar_ecc).

Methods:
  equiv_rand  : gen_lps_cover.py p q m cyc 1 t2 with t2 uniform in [1, m-1], seeds 0..4
  free_rand   : gen_lps_cover.py p q m free z_0 ... z_p with z_i uniform in [0, m-1], seeds 0..4
  equiv_best  : (p = 5 only) exhaustive over t2 in [1, m-1] and both primitive cube roots (--rk 1, --rk 2)

Usage: nice -n 10 python3 baselines.py [--skip-exhaustive]
Writes rows to c10/results.jsonl and the summary to c10/summary.json (stdout too)."""
import json, math, os, random, statistics, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS = '/home/user/degree-diameter/research/theorems/haar_families'
GEN = os.path.join(TOOLS, 'gen_lps_cover.py')
HECC = os.path.join(TOOLS, 'haar_ecc')
GRID = {5: [13, 17, 19, 23, 29], 7: [11, 13, 17, 19, 23]}
MS = [7, 13, 19, 31, 37, 43, 61]
MAXV = 1e7
SEEDS = range(5)
RESULTS = os.path.join(HERE, 'results.jsonl')
SKIP_EXH = '--skip-exhaustive' in sys.argv


def run_cell(p, q, m, gen_args):
    """Return dict with diam, full, vertices, excess (or error)."""
    V = q * (q * q - 1) * m
    g = subprocess.run(['python3', GEN, str(p), str(q), str(m)] + gen_args,
                       capture_output=True, text=True)
    if g.returncode:
        return {'error': 'gen: ' + g.stderr[-200:]}
    h = subprocess.run(['nice', '-n', '10', 'timeout', '900', HECC, 'pgl', str(q), str(m)],
                       input=g.stdout, capture_output=True, text=True)
    import re
    mm = re.search(r'Delta=(\d+) ecc_A=(\d+) ecc_B=(\d+) compA=(\d+) compB=(\d+)', h.stdout)
    if not mm:
        return {'error': 'haar_ecc: ' + (h.stdout + h.stderr)[-200:]}
    d, eA, eB, cA, cB = map(int, mm.groups())
    full = (cA == V and cB == V)
    diam = max(eA, eB)
    excess = diam - math.log(V / 2) / math.log(p)
    return {'vertices': V, 'full': full, 'diam': diam, 'excess': round(excess, 4), 'compA': cA, 'compB': cB}


def roots_count(m):
    return len([r for r in range(2, m) if (r * r + r + 1) % m == 0])


def main():
    t0 = time.time()
    out = open(RESULTS, 'w')
    rows = []
    for p in (5, 7):
        for q in GRID[p]:
            for m in MS:
                V = q * (q * q - 1) * m
                if V > MAXV:
                    continue
                assert roots_count(m) >= 2
                # (a) one random equivariant assignment per seed
                for s in SEEDS:
                    rng = random.Random(f'equiv,{p},{q},{m},{s}')
                    t2 = rng.randint(1, m - 1)
                    res = run_cell(p, q, m, ['cyc', '1', str(t2)])
                    row = dict(method='equiv_rand', p=p, q=q, m=m, seed=s, t2=t2, rk=1, **res)
                    rows.append(row); out.write(json.dumps(row) + '\n'); out.flush()
                # (b) one random free assignment per seed
                for s in SEEDS:
                    rng = random.Random(f'free,{p},{q},{m},{s}')
                    labs = [rng.randint(0, m - 1) for _ in range(p + 1)]
                    res = run_cell(p, q, m, ['free'] + [str(z) for z in labs])
                    row = dict(method='free_rand', p=p, q=q, m=m, seed=s, labels=labs, **res)
                    rows.append(row); out.write(json.dumps(row) + '\n'); out.flush()
                print(f'done random p={p} q={q} m={m} t={time.time()-t0:.0f}s', flush=True)
    # (c) exhaustive equivariant t2 search, p = 5 only
    if not SKIP_EXH:
        for q in GRID[5]:
            for m in MS:
                V = q * (q * q - 1) * m
                for rk in (1, 2):
                    for t2 in range(1, m):
                        res = run_cell(5, q, m, ['cyc', '1', str(t2), '--rk', str(rk)])
                        row = dict(method='equiv_best', p=5, q=q, m=m, t2=t2, rk=rk, **res)
                        rows.append(row); out.write(json.dumps(row) + '\n'); out.flush()
                print(f'done exhaustive q={q} m={m} t={time.time()-t0:.0f}s', flush=True)
    out.close()
    summarize(rows)
    print(f'total time {time.time()-t0:.0f}s', flush=True)


def summarize(rows):
    S = {}
    # (a) and (b): per seed, mean over FULL cells; then mean and sd over the 5 seeds
    for p in (5, 7):
        for meth in ('equiv_rand', 'free_rand'):
            per_seed = {}
            n_cells = {}
            for r in rows:
                if r.get('method') != meth or r['p'] != p or 'excess' not in r:
                    continue
                if not r['full']:
                    continue
                per_seed.setdefault(r['seed'], []).append(r['excess'])
            seed_means = [statistics.mean(v) for k, v in sorted(per_seed.items())]
            n_full = {k: len(v) for k, v in sorted(per_seed.items())}
            total_cells = len({(r['q'], r['m']) for r in rows if r.get('method') == meth and r['p'] == p})
            S[f'{meth}_p{p}'] = {
                'mean_over_seeds': round(statistics.mean(seed_means), 3),
                'sd_over_seeds': round(statistics.stdev(seed_means), 3) if len(seed_means) > 1 else None,
                'min_seed_mean': round(min(seed_means), 3), 'max_seed_mean': round(max(seed_means), 3),
                'seed_means': [round(x, 3) for x in seed_means],
                'full_cells_per_seed': n_full, 'cells_per_seed': total_cells,
            }
    # (c) exhaustive best per cell (p = 5)
    if any(r.get('method') == 'equiv_best' for r in rows):
        cells = {}
        for r in rows:
            if r.get('method') == 'equiv_best' and r['full']:
                key = (r['q'], r['m'])
                if key not in cells or r['excess'] < cells[key][0]:
                    cells[key] = (r['excess'], r['t2'], r['rk'], r['diam'])
        allcells = {(r['q'], r['m']) for r in rows if r.get('method') == 'equiv_best'}
        vals = [v[0] for v in cells.values()]
        S['equiv_best_p5'] = {
            'mean_over_cells': round(statistics.mean(vals), 3) if vals else None,
            'sd_over_cells': round(statistics.stdev(vals), 3) if len(vals) > 1 else None,
            'cells_with_full': len(cells), 'cells_total': len(allcells),
            'best_per_cell': {f'{k[0]},{k[1]}': {'excess': v[0], 't2': v[1], 'rk': v[2], 'diam': v[3]}
                              for k, v in sorted(cells.items())},
        }
    # invalid / errors
    S['errors'] = sum(1 for r in rows if 'error' in r)
    S['non_full_rows'] = sum(1 for r in rows if 'full' in r and not r['full'])
    with open(os.path.join(HERE, 'summary.json'), 'w') as f:
        json.dump(S, f, indent=1)
    print(json.dumps(S, indent=1))


if __name__ == '__main__':
    main()
