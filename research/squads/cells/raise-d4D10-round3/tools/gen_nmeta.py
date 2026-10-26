"""Non-split metacyclic candidates G = (Z_m . Z_k) x Z_n:  b a b^-1 = a^r,  b^k = a^s.
Conditions: gcd(r,m)=1, r^k = 1 (mod m), s(r-1) = 0 (mod m), gcd(m,k) > 1 (else the extension splits).
Normal form: b -> a^t b changes s by t*S_r (S_r = 1+r+...+r^(k-1)), and a -> a^u (u a unit) multiplies s by u.
So s may be taken to be a divisor d of m, and the extension is non-split iff g = gcd(S_r, m) does not divide d.
Output: N|nmeta m k r s n  for N in [LO, HI]."""
import sys, math
LO, HI = int(sys.argv[1]), int(sys.argv[2])
out = []
for N in range(LO, HI + 1):
    for n in range(1, N + 1):
        if N % n: continue
        M = N // n
        for k in range(2, M + 1):
            if M % k: continue
            m = M // k
            if m < 2 or math.gcd(m, k) == 1: continue
            divs = [d for d in range(1, m) if m % d == 0]
            for r in range(1, m):
                if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m: continue
                S = sum(pow(r, i, m) for i in range(k)) % m
                g = math.gcd(S, m)
                for d in divs:
                    if (d * (r - 1)) % m: continue
                    if d % g == 0: continue
                    out.append(f"{N}|nmeta {m} {k} {r} {d} {n}")
print("\n".join(out))
