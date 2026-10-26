# Metacyclic Z_m x|_r Z_k (order m*k in 802..900, k even), table via formula; scan each with ./scan (type A/B, D=10).
import sys, subprocess, numpy as np, math, random
random.seed(5)
D = 10
specs = []
for N in range(802, 901, 2):
    for k in range(2, N + 1, 2):
        if N % k: continue
        m = N // k
        if m < 3: continue
        if math.gcd(m, k) == 0: continue
        units = [r for r in range(1, m) if math.gcd(r, m) == 1] if m > 1 else [0]
        for r in units:
            if pow(r, k, m) != 1 % m: continue
            specs.append((m, k, r))
random.shuffle(specs)
print('candidate metacyclic specs', len(specs), flush=True)
out = []
LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 40
for (m, k, r) in specs[:LIMIT]:
    N = m * k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    idx = np.arange(N)
    a = idx % m; j = idx // m
    # x = a + m*j ; y = b + m*l
    A = a[:, None]; J = j[:, None]; B = a[None, :]; L = j[None, :]
    na = (A + pw[J] * B) % m
    nj = (J + L) % k
    T = na + m * nj
    fn = f'/home/user/degree-diameter/research/squads/b48/r4/h07/meta_{m}_{k}_{r}.tab'
    with open(fn, 'w') as fh:
        fh.write(f'{N}\n')
        for row in T:
            fh.write(' '.join(map(str, row.tolist())) + '\n')
    res = subprocess.run(['./scan', fn, str(D), '20000', '3'], capture_output=True, text=True, timeout=60).stdout.strip()
    print(m, k, r, res, flush=True)
    import os; os.remove(fn)
