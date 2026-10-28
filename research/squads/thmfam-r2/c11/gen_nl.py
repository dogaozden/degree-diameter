#!/usr/bin/env python3
"""c11: nonlinear equivariant label rules for LPS x Z_m covers (self-contained; same matrices, S_p reps and r as
gen_lps_cover.py).  Rule family, with r of order 3 mod m and sigma(a0,a1,a2,a3) = (a0,a3,a1,a2):
  slot   z(alpha) = F(a1) + F(a2) r + F(a3) r^2   mod m       (any F: z(sigma a) = r z(a) exactly on the quaternion)
  coupled z(alpha) = F(a0,a1) + F(a0,a2) r + F(a0,a3) r^2     (a0 is sigma-fixed, so also equivariant)
Fixed letters a1=a2=a3 give F(a)(1+r+r^2)=0 (r^2+r+1=0 mod m).  Rules (name: F):
  lin: a | sq: a^2 | cube: a^3 | absa: a|a| | sgn: sign(a) | mod3: a mod 3 | par: a mod 2 | tri: a(a+1)/2
  inv: a^{-1} mod m (0 if not a unit) | sqa0: coupled a0*a | sgna0: coupled sign(a)*sign(a0) | mixc: coupled a0*a*a
  | cubic: a^3 + 2a (odd) | ab: coupled a0*a + a (not a shift)
  | pw:A:B: F(a) = A (a>0), B (a<0), 0 (a=0)  (integer two-sign family; used for the p=5 scan)
Usage: gen_nl.py p q m RULE [--rk k]   (prints p+1 lines "a b c d z"; --show prints the S_p reps to stderr)"""
import sys, math
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
SGN = lambda x: (x > 0) - (x < 0)
SLOT = {
    'lin':  lambda a: a,
    'sq':   lambda a: a * a,
    'cube': lambda a: a ** 3,
    'absa': lambda a: a * abs(a),
    'sgn':  lambda a: SGN(a),
    'mod3': lambda a: a % 3,
    'par':  lambda a: a % 2,
    'tri':  lambda a: a * (a + 1) // 2,
    'cubic': lambda a: a ** 3 + 2 * a,
}
COUPLED = {
    'sqa0':  lambda a0, a: a0 * a,
    'sgna0': lambda a0, a: SGN(a) * SGN(a0),
    'mixc':  lambda a0, a: a0 * a * a,
    'ab':    lambda a0, a: a0 * a + a,
}
def main():
    args = sys.argv[1:]
    rk = 1
    if '--rk' in args:
        i = args.index('--rk'); rk = int(args[i + 1]); del args[i:i + 2]
    show = '--show' in args
    if show: args.remove('--show')
    p, q, m, rule = int(args[0]), int(args[1]), int(args[2]), args[3]
    x = y = None
    for a in range(q):
        for b in range(q):
            if (a*a + b*b + 1) % q == 0: x, y = a, b; break
        if x is not None: break
    S = lps_set(p)
    roots = [r for r in range(2, m) if (r*r + r + 1) % m == 0] if m > 3 else []
    r = roots[rk - 1] if len(roots) >= rk else 0
    if rule.startswith('pw:'):  # pw:A:B  ->  F(a) = A if a>0, B if a<0, 0 if a=0  (the two-value family, see NOTES.md)
        _, A_, B_ = rule.split(':'); A_, B_ = int(A_), int(B_)
        F = lambda a: A_ if a > 0 else (B_ if a < 0 else 0)
        coupled = False
    elif rule == 'inv':
        F = lambda a: pow(a, -1, m) if math.gcd(a, m) == 1 else 0
        coupled = False
    elif rule in SLOT:
        F = lambda a, f=SLOT[rule]: f(a)
        coupled = False
    elif rule in COUPLED:
        coupled = True
    else:
        sys.exit('unknown rule ' + rule)
    import math  # noqa (used by inv)
    lab = {}
    for al in S:
        a0, a1, a2, a3 = al
        if coupled:
            G = COUPLED[rule]
            z = G(a0, a1) + G(a0, a2) * r + G(a0, a3) * r * r
        else:
            z = F(a1) + F(a2) * r + F(a3) * r * r
        lab[al] = z % m
    if show: print('r =', r, 'S =', S, file=sys.stderr)
    for al in S:
        a0, a1, a2, a3 = al
        M = ((a0 + a1*x + a3*y) % q, (-a1*y + a2 + a3*x) % q, (-a1*y - a2 + a3*x) % q, (a0 - a1*x - a3*y) % q)
        print(*M, lab[al])
main()
