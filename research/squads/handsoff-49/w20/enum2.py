# Candidate list with split flag: fields N m k r s d dk type, sorted by dk (small abelianization first).
import math, sys
LO, HI, BOUND = 2486, 2520, 309
rows = []
for N in range(LO, HI + 1):
    for m in range(1, N + 1):
        if N % m: continue
        k = N // m
        if k < 2: continue
        seen = set()
        for r in range(1, m):
            if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m: continue
            d = math.gcd(r - 1, m)
            if d * k > BOUND: continue
            sub = frozenset(pow(r, t, m) for t in range(k))
            if sub in seen: continue
            seen.add(sub)
            sigma = sum(pow(r, j, m) for j in range(k)) % m
            T = [s for s in range(m) if (s * (r - 1)) % m == 0]
            units = [u for u in range(1, m) if math.gcd(u, m) == 1]
            par = {s: s for s in T}
            def f(x):
                while par[x] != x:
                    par[x] = par[par[x]]; x = par[x]
                return x
            for s in T:
                y = (s + sigma) % m
                par[f(s)] = f(y)
                for u in units:
                    par[f(s)] = f((u * s) % m)
            z0 = f(0)
            for s in sorted({f(s) for s in T}):
                rows.append((N, m, k, r, s, d, d * k, "split" if s == z0 else "ns"))
# split classes: rep 0 (canonical meta); ns: keep rep s
out = []
for row in rows:
    N, m, k, r, s, d, dk, typ = row
    if typ == "split":
        out.append((dk, N, m, k, r, 0, d, "split"))
    else:
        out.append((dk, N, m, k, r, s, d, "ns"))
out.sort()
with open("cand_sorted.tsv", "w") as fh:
    fh.write("dk\tN\tm\tk\tr\ts\td\ttype\n")
    for t in out: fh.write("\t".join(map(str, t)) + "\n")
print(len(out), "classes; split", sum(1 for t in out if t[7]=="split"), "ns", sum(1 for t in out if t[7]=="ns"))
