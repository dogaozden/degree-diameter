#!/usr/bin/env python3
"""Card c2 wrapper for cover_score.py --gen. Usage: c2_rule.py p q m RULE RK
RULE is one of the t2 functions below (cyc 1 t2 with t2 = f(m, r) mod m), or 'rand:SEED' (baseline: t2 uniform in
[1, m-1], seeded by (seed, q, m)). RK selects the order-3 root r (gen_lps_cover --rk). Prints the generator lines."""
import sys, random, subprocess, os
HERE = os.path.dirname(os.path.abspath(__file__))
GEN = '/home/user/degree-diameter/research/theorems/haar_families/gen_lps_cover.py'
T2 = {
    'const2': lambda m, r: 2,
    'm-1': lambda m, r: m - 1,
    'm-2': lambda m, r: m - 2,
    'r+1': lambda m, r: r + 1,
    'r-1': lambda m, r: r - 1,
    '2r': lambda m, r: 2 * r,
    '(m-1)/2': lambda m, r: (m - 1) // 2,
    'r^2+2': lambda m, r: r * r + 2,
    'const3': lambda m, r: 3,
    'const5': lambda m, r: 5,
    'const4': lambda m, r: 4,
    'r^2': lambda m, r: r * r,
    '2r+1': lambda m, r: 2 * r + 1,
    'r+2': lambda m, r: r + 2,
}
def main():
    p, q, m = map(int, sys.argv[1:4]); rule = sys.argv[4]; rk = int(sys.argv[5])
    roots = [x for x in range(2, m) if (x * x + x + 1) % m == 0] if m > 3 else []
    r = roots[rk - 1] if len(roots) >= rk else 0
    if rule.isdigit():
        rule = list(T2)[int(rule)]
    if rule.startswith('rand:'):
        seed = int(rule.split(':')[1])
        t2 = random.Random(seed * 1000003 + q * 1009 + m).randrange(1, m)
    else:
        t2 = T2[rule](m, r) % m
    cmd = [sys.executable, GEN, str(p), str(q), str(m), 'cyc', '1', str(t2), '--rk', str(rk)]
    g = subprocess.run(cmd, capture_output=True, text=True)
    if g.returncode:
        sys.stderr.write(g.stderr); sys.exit(1)
    sys.stdout.write(g.stdout)
    sys.stderr.write(f'c2_rule rule={rule} t2={t2} r={r} rk={rk}\n')
main()
