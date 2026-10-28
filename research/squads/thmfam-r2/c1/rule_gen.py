#!/usr/bin/env python3
"""Generator for card c1: LPS(5) x Z_m with cycle labels (1, r, r^2) on the first 3-cycle and (t2, t2 r, t2 r^2) on the
second, where t2 is a fixed function of (m, r) (named rule) or a seeded random unit-range draw.  Fixed letters get 0.
Wrapper around gen_lps_cover.py (same r as there: the rk-th root of r^2+r+1 mod m, r in [2, m)).
Usage: rule_gen.py p q m NAME [--rk k] [--seed s]
  NAME in: 2 m-1 m-2 r+1 r-1 2r half r2+2 3 5 4 r2 2r+1 half+ r+2 3r rand
  half = (m-1)/2, half+ = (m+1)/2, r2 = r^2, rand = uniform on 1..m-1 seeded by (q, m, s)."""
import sys, os, subprocess, random
HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS = '/home/user/degree-diameter/research/theorems/haar_families'
args = sys.argv[1:]
rk = 1; seed = 1
if '--rk' in args: i = args.index('--rk'); rk = int(args[i + 1]); del args[i:i + 2]
if '--seed' in args: i = args.index('--seed'); seed = int(args[i + 1]); del args[i:i + 2]
p, q, m, name = int(args[0]), int(args[1]), int(args[2]), args[3]
roots = [r for r in range(2, m) if (r * r + r + 1) % m == 0] if m > 3 else []
if len(roots) < rk: sys.exit(f'no root #{rk} of r^2+r+1 mod {m}')
r = roots[rk - 1]
rules = {
    '2': lambda: 2, 'm-1': lambda: m - 1, 'm-2': lambda: m - 2,
    'r+1': lambda: r + 1, 'r-1': lambda: r - 1, '2r': lambda: 2 * r,
    'half': lambda: (m - 1) // 2, 'r2+2': lambda: r * r + 2, '3': lambda: 3, '5': lambda: 5,
    '4': lambda: 4, 'r2': lambda: r * r, '2r+1': lambda: 2 * r + 1, 'half+': lambda: (m + 1) // 2,
    'r+2': lambda: r + 2, '3r': lambda: 3 * r,
    'rand': lambda: random.Random(q * 1000003 + m * 1009 + seed).randrange(1, m),
}
t2 = rules[name]() % m
out = subprocess.run([sys.executable, f'{TOOLS}/gen_lps_cover.py', str(p), str(q), str(m), 'cyc', '1', str(t2),
                      '--rk', str(rk)], capture_output=True, text=True)
if out.returncode: sys.exit(out.stderr)
sys.stdout.write(out.stdout)
