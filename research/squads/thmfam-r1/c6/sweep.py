#!/usr/bin/env python3
"""c6 sweep: for each (q, m) try every t2 in [1,m-1] and both r; record component size and exact diameter.
usage: sweep.py q m1 [m2 ...]   -> appends JSON lines to results.jsonl"""
import subprocess, sys, json, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen_c6
H = '/home/user/degree-diameter/research/theorems/haar_families/haar_ecc'
q = int(sys.argv[1]); ms = [int(x) for x in sys.argv[2:]]
gens_cache = gen_c6.lps_gens(q)
out = open(os.path.join(HERE, 'results.jsonl'), 'a')
for m in ms:
    if not all(m % d for d in range(2, int(m**.5) + 1)) is True:
        pass
    target = q * (q * q - 1) * m
    best = None
    for rsel in (0, 1):
        for t2 in range(1, m):
            z = gen_c6.labels(gens_cache, m, t2, rsel)
            lines = "\n".join(f"{a} {b} {c} {d} {z[i]}" for i, (qu, (a, b, c, d)) in enumerate(gens_cache)) + "\n"
            r = subprocess.run(['nice', '-n', '10', 'timeout', '900', H, 'pgl', str(q), str(m)],
                               input=lines, capture_output=True, text=True)
            s = r.stdout
            import re
            mm = re.search(r'compA=(\d+) compB=(\d+) .* diam=(\d+)', s)
            if not mm:
                rec = dict(q=q, m=m, t2=t2, rsel=rsel, err=s[-200:] + r.stderr[-200:])
            else:
                cA, cB, diam = int(mm.group(1)), int(mm.group(2)), int(mm.group(3))
                rec = dict(q=q, m=m, t2=t2, rsel=rsel, compA=cA, compB=cB, target=target,
                           full=(cA == target and cB == target), diam=diam)
            out.write(json.dumps(rec) + "\n"); out.flush()
out.close()
