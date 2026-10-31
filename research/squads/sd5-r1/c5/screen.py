# screen.py: metacyclic Z_n:Z_k (r^k=1 mod n) of order N in [lo,hi], lift22 with valency 6 (DELTA=6), a=A, short anneal.
import sys, subprocess, os, re
from math import gcd
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mkmeta import build
lo, hi, A, secs = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
tmpd = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'tmp')
env = dict(os.environ, DELTA='6', SECS=secs, SEED='1', TMPDIR=tmpd)
seen = set()
for N in range(lo, hi + 1):
    for k in range(2, N + 1):
        if N % k: continue
        n = N // k
        if n < 3: continue
        rs = [r for r in range(2, n) if gcd(r, n) == 1 and pow(r, k, n) == 1 % n]
        # keep a few r per (n,k): smallest and the largest (r and -1 types)
        pick = sorted(set(rs[:3] + rs[-2:])) if len(rs) > 5 else rs
        for r in pick:
            if (n, k, r) in seen: continue
            seen.add((n, k, r))
            path = os.path.join(tmpd, f'meta_{n}_{k}_{r}.ht')
            Nn, mul, inv, ninv = build(n, k, r)
            with open(path, 'w') as f:
                f.write(f"{Nn} {ninv}\n")
                for row in mul: f.write(" ".join(map(str, row)) + "\n")
                f.write(" ".join(map(str, inv)) + "\n")
            out = subprocess.run(['nice', '-n', '15', './lift22', path, str(A), os.path.join(tmpd, f'meta_{n}_{k}_{r}_a{A}.edges')],
                                 env=env, capture_output=True, text=True, timeout=600).stdout.strip().splitlines()
            line = out[-1] if out else 'NONE'
            m = re.search(r'best (\d+) odd_ok (\d)', line)
            best, odd = (int(m.group(1)), int(m.group(2))) if m else (-1, -1)
            print(f"N={Nn} n={n} k={k} r={r} a={A} best={best} odd_ok={odd}", flush=True)
            if best != 0 or odd != 1:
                os.remove(os.path.join(tmpd, f'meta_{n}_{k}_{r}_a{A}.edges')) if os.path.exists(os.path.join(tmpd, f'meta_{n}_{k}_{r}_a{A}.edges')) else None
            os.remove(path)
