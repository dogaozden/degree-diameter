import sys, math, random
def meta_list(N):
    out = []
    for k in range(1, N + 1):
        if N % k: continue
        m = N // k
        if m == 1: out.append((1, k, 0, False)); continue
        for r in range(1, m):
            if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m: continue
            out.append((m, k, r, r % m != 1))
    return out
lo, hi = int(sys.argv[1]), int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
def spec(t):
    m, k, r, _ = t
    return f"meta:{k}:1:1" if m == 1 else f"meta:{m}:{k}:{r}"
pairs = []
for a in range(2, hi // 2 + 1):
    for b in range(a, hi // 2 + 1):
        N = a * b
        if N < lo or N > hi: continue
        for t1 in meta_list(a):
            for t2 in meta_list(b):
                if not (t1[3] or t2[3]): continue
                pairs.append((N, f"prod:{spec(t1)}/{spec(t2)}"))
single = [(N, f"meta:{m}:{k}:{r}") for N in range(lo, hi + 1) for (m, k, r, nab) in meta_list(N) if nab]
print(len(pairs), len(single), file=sys.stderr)
pick = [p for p in rng.sample(pairs, 12)]
pick += rng.sample(single, 6)
for N, s in pick: print(N, s)
