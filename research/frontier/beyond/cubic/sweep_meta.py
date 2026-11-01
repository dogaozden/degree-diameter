import sys, subprocess, math, os
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/tools')
import groups
D = int(sys.argv[1]); lo, hi = int(sys.argv[2]), int(sys.argv[3])
def order_mod(r, m):
    if math.gcd(r, m) != 1: return 0
    x, o = r % m, 1
    while x != 1 % m:
        x = x * r % m; o += 1
        if o > m: return 0
    return o
specs = []
for k in range(2, 41):
    for m in range(max(3, lo // k), hi // k + 1):
        N = m * k
        if N < lo or N > hi: continue
        rs = [r for r in range(2, m) if order_mod(r, m) == k]
        if not rs: continue
        specs.append((N, m, k, rs[0]))
specs.sort()
print(len(specs), "groups", file=sys.stderr)
for N, m, k, r in specs:
    T = groups.table(f"meta {m} {k} {r}")
    fn = f"t_{m}_{k}_{r}.bin"
    with open(fn, 'wb') as f:
        import numpy as np
        f.write(np.array([N], dtype=np.int32).tobytes()); f.write(T.astype(np.uint16).tobytes())
    out = subprocess.run(["./exh3", fn, str(D), f"hit_D{D}_meta_{m}_{k}_{r}"], capture_output=True, text=True, timeout=300).stdout
    line = [l for l in out.splitlines() if l.startswith("GROUP")]
    print(f"meta {m} {k} {r} | {line[0] if line else out[-200:]}", flush=True)
    os.remove(fn)
