#!/usr/bin/env python3
"""Card c3: label rules (t1,t2,t3,t4) on the four 3-cycles of LPS(p) x Z_m covers, p = 11 and p = 13.
Each cell: gen_lps_cover.py p q m cyc t1..t4 | haar_ecc pgl q m.  Excess = diam - log_p(V/2), V = q(q^2-1)m.
Score per rule = mean excess over FULL cells (compA == V).  Writes c3/results.jsonl; prints a summary.
Usage: python3 run_c3.py [p ...]   (default: 11 13)"""
import subprocess, math, re, json, os, random, sys
HERE = os.path.dirname(os.path.abspath(__file__))
TH = '/home/user/degree-diameter/research/theorems/haar_families'
GEN = os.path.join(TH, 'gen_lps_cover.py'); ECC = os.path.join(TH, 'haar_ecc')
MS = [7, 13, 19, 31, 37, 43, 61, 73]
GRID = {11: [13, 17, 19, 23], 13: [17, 19, 23, 29]}

def root(m):
    # same choice as gen_lps_cover.py with --rk 1: smallest r in [2, m) with r^2 + r + 1 = 0 mod m
    return [r for r in range(2, m) if (r * r + r + 1) % m == 0][0]

def inv2(m):
    return (m + 1) // 2  # inverse of 2 mod odd m

RULES = {  # name -> (m, r) -> [t1, t2, t3, t4]
    'lit_1234': lambda m, r: [1, 2, 3, 4],
    'lit_1m1_2m2': lambda m, r: [1, m - 1, 2, m - 2],
    'lit_1r1_2r1': lambda m, r: [1, r + 1, 2, 2 * r + 1],
    'pow_g2': lambda m, r: [1, 2, 4, 8],
    'pow_g3': lambda m, r: [1, 3, 9, 27],
    'pow_gr1': lambda m, r: [1, r + 1, (r + 1) ** 2, (r + 1) ** 3],
    'O_all_equal': lambda m, r: [1, 1, 1, 1],
    'O_alt_pm1': lambda m, r: [1, m - 1, 1, m - 1],
    'O_1_r_r2_1': lambda m, r: [1, r, r * r, 1],
    'O_0123': lambda m, r: [0, 1, 2, 3],
    'O_1_2_r_2r': lambda m, r: [1, 2, r, 2 * r],
    'O_1_r_2_2r': lambda m, r: [1, r, 2, 2 * r],
    'O_1_m2_4_m8': lambda m, r: [1, m - 2, 4, m - 8],
    'O_primes_1235': lambda m, r: [1, 2, 3, 5],
    'O_half': lambda m, r: [1, inv2(m), 2, 1],
    'O_mix': lambda m, r: [1, r + 2, r * r + 1, 2 * r],
    'O_AP_step_r': lambda m, r: [1, 1 + r, 1 + 2 * r, 1 + 3 * r],
    'O_2357': lambda m, r: [2, 3, 5, 7],
    'O_1_2r1_r1_r2': lambda m, r: [1, 2 * r + 1, r + 1, r * r],
    'O_1_2r_r2_3': lambda m, r: [1, 2 * r, r * r, 3],
}

def ecc_of(p, q, m, lines):
    r = subprocess.run([ECC, 'pgl', str(q), str(m)], input=lines, capture_output=True, text=True)
    mm = re.search(r'ecc_A=(\d+) ecc_B=(\d+) compA=(\d+) compB=(\d+)', r.stdout)
    if not mm:
        return {'err': 'haar_ecc failed: ' + r.stdout[-120:]}
    eA, eB, cA, cB = map(int, mm.groups())
    V = q * (q * q - 1) * m
    diam = max(eA, eB)
    return {'V': V, 'full': cA == V, 'diam': diam, 'excess': round(diam - math.log(V / 2) / math.log(p), 4),
            'compA': cA, 'ecc_A': eA, 'ecc_B': eB}

def gen_and_score(p, q, m, args):
    g = subprocess.run([sys.executable, GEN, str(p), str(q), str(m)] + args, capture_output=True, text=True)
    if g.returncode:
        return {'err': 'gen failed: ' + g.stderr[-120:]}
    return ecc_of(p, q, m, g.stdout)

def cells_for(p):
    return [(q, m) for q in GRID[p] for m in MS if q * (q * q - 1) * m <= 1e7]

def main():
    ps = [int(x) for x in sys.argv[1:]] or [11, 13]
    out = open(os.path.join(HERE, 'results.jsonl'), 'w')
    summary = []  # (p, rule, mean, n_full, n_cells, per_seed)
    for p in ps:
        cells = cells_for(p)
        def record(row):
            out.write(json.dumps(row) + '\n')
        def finish(name, rows_by_seed):
            per_seed, nfs = [], []
            for rows in rows_by_seed:
                ok = [x['excess'] for x in rows if x.get('full')]
                per_seed.append(sum(ok) / len(ok) if ok else float('nan'))
                nfs.append(len(ok))
            summary.append((p, name, sum(per_seed) / len(per_seed), nfs, len(cells), per_seed))
        # arithmetic rule
        rows = []
        for q, m in cells:
            row = gen_and_score(p, q, m, ['arith']); row.update(p=p, q=q, m=m, rule='arith'); rows.append(row); record(row)
        finish('arith', [rows])
        # named / other cyc rules
        for name, f in RULES.items():
            rows = []
            for q, m in cells:
                r = root(m); ts = [t % m for t in f(m, r)]
                row = gen_and_score(p, q, m, ['cyc'] + [str(t) for t in ts])
                row.update(p=p, q=q, m=m, rule=name, ts=ts); rows.append(row); record(row)
            finish(name, [rows])
        # baseline: random equivariant cyc labels, 3 seeds
        seeds = []
        for seed in (1, 2, 3):
            rows = []
            for q, m in cells:
                rng = random.Random(10007 * seed + 31 * q + m)
                ts = [rng.randrange(m) for _ in range(4)]
                row = gen_and_score(p, q, m, ['cyc'] + [str(t) for t in ts])
                row.update(p=p, q=q, m=m, rule='baseline_random_cyc', seed=seed, ts=ts); rows.append(row); record(row)
            seeds.append(rows)
        finish('baseline_random_cyc', seeds)
        # baseline: random free labels (one per generator), 3 seeds
        seeds = []
        for seed in (1, 2, 3):
            rows = []
            for q, m in cells:
                rng = random.Random(20011 * seed + 17 * q + m)
                labs = [rng.randrange(m) for _ in range(p + 1)]
                row = gen_and_score(p, q, m, ['free'] + [str(x) for x in labs])
                row.update(p=p, q=q, m=m, rule='baseline_random_free', seed=seed); rows.append(row); record(row)
            seeds.append(rows)
        finish('baseline_random_free', seeds)
    out.close()
    for p, name, mean, nfs, ncell, per_seed in sorted(summary, key=lambda x: (x[0], x[2] if x[2] == x[2] else 1e9)):
        extra = '' if per_seed is None or len(per_seed) == 1 else ' seeds=%s' % [round(x, 4) for x in per_seed]
        print(f"p={p} {name:24s} mean_excess={mean:.4f} n_full={nfs} of {ncell}{extra}")

if __name__ == '__main__':
    main()
