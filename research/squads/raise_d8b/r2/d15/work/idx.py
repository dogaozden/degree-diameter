# Reproduce haar_sym build_matrix enumeration order for PSL(2,41) and SL(2,5) and find the
# index of (g, I) with g of projective order 5 in PSL(2,41).
def enum(q, psl):
    reps = []; idx = {}
    inv = {a: pow(a, q - 2, q) for a in range(1, q)}
    neg = lambda x: (-x) % q
    for t in range(q * q * q):
        a = t // (q * q); b = t // q % q; c = t % q
        if a:
            dd = inv[a] * (1 + b * c) % q
        else:
            if not b: continue
            dd = c; c = neg(inv[b])
        key = (a, b, c, dd)
        if key in idx: continue
        n = len(reps); reps.append(key); idx[key] = n
        if psl: idx[(neg(a), neg(b), neg(c), neg(dd))] = n
    return reps, idx
def mul(A, B, q):
    a1, b1, c1, d1 = A; a2, b2, c2, d2 = B
    return ((a1*a2 + b1*c2) % q, (a1*b2 + b1*d2) % q, (c1*a2 + d1*c2) % q, (c1*b2 + d1*d2) % q)
q = 41
reps, idx = enum(q, True)
print("PSL order", len(reps))
sl_reps, sl_idx = enum(5, False)
print("SL5 order", len(sl_reps), "ident", sl_idx[(1, 0, 0, 1)])
ident2 = sl_idx[(1, 0, 0, 1)]
# element of order 10 in F_41^*, lambda; M = diag(lam, lam^-1) has M^5 = -I, projective order 5
lam = next(x for x in range(2, q) if pow(x, 10, q) == 1 and pow(x, 5, q) != 1)
M = (lam, 0, 0, pow(lam, q - 2, q))
P = (1, 0, 0, 1); powers = []
for k in range(1, 7):
    P = mul(P, M, q); powers.append(P)
print("powers", powers)
i1 = idx[M]
print("g index in PSL", i1, "lam", lam)
print("prod index (g,I) =", i1 * 120 + ident2)
