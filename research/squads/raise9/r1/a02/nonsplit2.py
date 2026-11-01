import math, sys, pickle
specs = pickle.load(open('nonsplit_specs.pkl', 'rb'))
seen = {}
for (N, m, k, r, s) in specs:
    sig = sum(pow(r, t, m) for t in range(k)) % m
    g = math.gcd(sig, m) if sig else m
    if s % g == 0: continue   # coset contains 0: split
    units = [t for t in range(1, m) if math.gcd(t, m) == 1]
    key = (N, m, k, r, g, min((t * s) % g for t in units) if g > 1 else 0)
    # r-equivalence: r -> r^j (gcd(j,k)=1) only changes the labelling; keep r as is but dedupe r by its class
    rk = r
    key = (N, m, k, rk, g, min((t * s) % g for t in units) if g > 1 else 0)
    if key not in seen: seen[key] = (N, m, k, r, s)
print(len(seen), file=sys.stderr)
pickle.dump(list(seen.values()), open('nonsplit_dedup.pkl', 'wb'))
