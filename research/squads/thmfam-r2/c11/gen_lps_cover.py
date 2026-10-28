#!/usr/bin/env python3
"""Generator lines "a b c d z" for LPS x Z_m covers: matrices psi(alpha), alpha in S_p (as in lps_haar.c, same x, y),
with Z_m labels by a rule.  r = an element of order 3 mod m (r^2 + r + 1 = 0 mod m; the smallest such r >= 2, or the
k-th one with --rk k).  sigma(a0,a1,a2,a3) = (a0,a3,a1,a2) is the order-3 symmetry (HAAR_FAMILIES.md Thm 2.6).
Rules:
  arith            z(alpha) = a1 + a2 r + a3 r^2 mod m   (equivariant: z(sigma alpha) = r z(alpha); fixed letters get 0)
  cyc t1 t2 ...    3-cycles in canonical order get (t, r t, r^2 t); fixed letters 0
  free z0 z1 ...   explicit labels in generator order
  zero             all labels 0 (the LPS graph itself; use m = 1)
Usage: gen_lps_cover.py p q m RULE [args] [--rk k]      (prints p+1 lines; --show prints the cycles to stderr)"""
import sys
def isqrt(n):
    r = int(n ** .5)
    while r * r > n: r -= 1
    while (r + 1) * (r + 1) <= n: r += 1
    return r
def lps_set(p):
    S = []
    R = isqrt(p) + 1
    for a0 in range(-R, R + 1):
        for a1 in range(-R, R + 1):
            for a2 in range(-R, R + 1):
                r2 = p - a0*a0 - a1*a1 - a2*a2
                if r2 < 0: continue
                a3 = isqrt(r2)
                if a3 * a3 != r2: continue
                for b3 in ([a3, -a3] if a3 else [0]):
                    if p % 4 == 1: ok = a0 > 0 and a0 % 2 == 1 and a1 % 2 == 0 and a2 % 2 == 0 and b3 % 2 == 0
                    else: ok = a0 % 2 == 0 and a1 % 2 and a2 % 2 and b3 % 2 and (a0 > 0 or (a0 == 0 and a1 > 0))
                    if ok: S.append((a0, a1, a2, b3))
    assert len(S) == p + 1, (len(S), p)
    return S
def canon(al):  # representative of +-alpha in S_p
    a0, a1, a2, a3 = al
    neg = (-a0, -a1, -a2, -a3)
    return al
def main():
    args = sys.argv[1:]
    rk = 1
    if '--rk' in args:
        i = args.index('--rk'); rk = int(args[i + 1]); del args[i:i + 2]
    show = '--show' in args
    if show: args.remove('--show')
    p, q, m, rule = int(args[0]), int(args[1]), int(args[2]), args[3]; rest = [int(t) for t in args[4:]]
    x = y = None
    for a in range(q):
        for b in range(q):
            if (a*a + b*b + 1) % q == 0: x, y = a, b; break
        if x is not None: break
    S = lps_set(p)
    Sset = set(S)
    def norm_rep(al):
        if al in Sset: return al
        neg = tuple(-t for t in al)
        assert neg in Sset, al
        return neg
    sig = lambda al: (al[0], al[3], al[1], al[2])
    roots = [r for r in range(2, m) if (r*r + r + 1) % m == 0] if m > 3 else []
    r = roots[rk - 1] if len(roots) >= rk else 0
    # cycles
    seen = set(); cycles = []; fixed = []
    for al in sorted(S):
        if al in seen: continue
        b = norm_rep(sig(al))
        if b == al: fixed.append(al); seen.add(al); continue
        c = [al, b, norm_rep(sig(b))]
        seen |= set(c); cycles.append(c)
    lab = {}
    if rule == 'zero':
        lab = {al: 0 for al in S}
    elif rule == 'arith':
        for al in S:
            # labels of +-alpha: use the representative in S_p (sign flips z by -1 for the pair; we use the S_p element)
            lab[al] = (al[1] + al[2] * r + al[3] * r * r) % m
    elif rule == 'cyc':
        assert len(rest) >= len(cycles), f"need {len(cycles)} cycle labels"
        for al in fixed: lab[al] = 0
        for c, t in zip(cycles, rest):
            for e, al in enumerate(c): lab[al] = t * pow(r, e, m) % m
    elif rule == 'free':
        assert len(rest) == len(S)
        for al, t in zip(S, rest): lab[al] = t % m
    else:
        sys.exit('unknown rule')
    if show:
        print('r =', r, 'fixed', fixed, 'cycles', cycles, file=sys.stderr)
    for al in S:
        a0, a1, a2, a3 = al
        M = ((a0 + a1*x + a3*y) % q, (-a1*y + a2 + a3*x) % q, (-a1*y - a2 + a3*x) % q, (a0 - a1*x - a3*y) % q)
        print(*M, lab[al])
main()
