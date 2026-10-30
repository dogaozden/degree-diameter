#!/usr/bin/env python3
"""Referee checks for D7_THEOREMS.md: closed forms, slot counts, Theorems 2.1 and 2.2, condition (*), the build
layouts of Section 2.  Written from the note's statements only (no code of the note is imported)."""
import itertools, random, sys
from fractions import Fraction

def N(q): return (q + 1) * (q**4 + q**2 + 1)
def P(q): return (q + 1) * (q**3 + 1)
def Lam(q): return q**4 + q**2 + q
def ppowers(lim):
    out = []
    for n in range(2, lim + 1):
        m = n; p = None
        for d in range(2, int(n**0.5) + 1):
            if m % d == 0: p = d; break
        if p is None: out.append(n); continue
        while m % p == 0: m //= p
        if m == 1: out.append(n)
    return out

def fg(arcs, L):
    """arcs: set of (i,j) meaning i->j; returns out-lists, in-lists"""
    out = [[] for _ in range(L)]; inn = [[] for _ in range(L)]
    for (i, j) in arcs: out[i].append(j); inn[j].append(i)
    return out, inn

def slots(T, arcs, Pv, Lv, m):
    L = len(T); al = [0]*L; be = [0]*L
    for (i, j) in arcs:
        if T[i] != T[j]: s = Pv if T[i] == 'H' else Lv
        else: s = m
        al[i] += s; be[j] += s
    return al, be

def rot(L):
    k = (L - 1)//2
    return {(j, (j + i) % L) for j in range(L) for i in range(1, k + 1)}

def alt(k):
    return ''.join('H' if j % 2 == 0 else 'D' for j in range(2*k + 1))

def fcount(T, arcs):
    L = len(T); f = [0]*L; g = [0]*L
    for (i, j) in arcs:
        if T[i] != T[j]: f[i] += 1; g[j] += 1
    return f, g

ok_all = True
def check(cond, msg):
    global ok_all
    if not cond: ok_all = False; print('FAIL', msg)

# 0. basic identities
for q in ppowers(400):
    check(P(q) == q**4 + q**3 + q + 1, 'P')
    check(P(q) - Lam(q) == q**3 - q**2 + 1, 'P-Lam')
    check(N(q) - P(q) == q**5 + q**2 == q*(q**4 + q), 'N-P')
    check(q*(q + 1) + q**2*(q**2 - 1) == q**4 + q, 'Lv+W')
    check(q*(q + 1) + q**2*(q**2 - 1) + q**2 == Lam(q), 'R_L size')
    check((q + 1)*q**4 - (q + 1)*q**3 == q**3*(q**2 - 1), 'free points')
print('0. identities P, P-Lam, N-P, |L_v|+|W|, |R_L|, free points: ok for prime powers <= 400')

# 1. Theorem 2.2: f_j of the alternating layout, closed forms of the minima, k <= 40
for k in range(1, 41):
    L = 2*k + 1; T = alt(k); A = rot(L); f, g = fcount(T, A)
    a = k // 2
    for j in range(L):
        if j <= k: exp = -(-k // 2)
        else:
            t = j - k
            if k % 2 == 0: exp = k//2 if t % 2 == 0 else k//2 + 1
            else: exp = (k - 1)//2 if t % 2 == 1 else (k + 1)//2
        check(f[j] == exp, 'Thm2.2 f k=%d j=%d' % (k, j))
        check(g[j] == f[2*k - j], 'Thm2.2 g k=%d j=%d' % (k, j))
    # minima with symbolic-ish numbers: use several (q, m) satisfying (*)
    for q in (11, 13, 16, 101, 1009):
        for m in sorted({q*q + 1, 768 if q == 11 else q*q + 1, 792 if q == 13 else q*q + 1}):
            Pv, Lv = P(q), Lam(q)
            star = Pv >= Lv >= m and Lv - m >= a*(Pv - Lv)
            al, be = slots(T, A, Pv, Lv, m)
            if k % 2 == 0:
                ea, eb = a*(Lv + m), a*(Lv + m)
            else:
                ea, eb = a*Pv + (a + 1)*m, a*Lv + (a + 1)*m
            if star:
                check(min(al) == ea and min(be) == eb, 'Thm2.2 minima k=%d q=%d m=%d' % (k, q, m))
print('1. Theorem 2.2: f_j, g_j = f_{2k-j} for k <= 40; minima equal the closed forms whenever (*) holds')

# 2. (*) ranges
def kmax_star(q, m):
    Pv, Lv = P(q), Lam(q); best = 0
    for k in range(1, 2*q + 10):
        a = k // 2
        if Lv - m >= a*(Pv - Lv): best = k
        else: break
    return best
print('2. (*) holds up to k =', kmax_star(11, 768), 'at q=11 m=768;', kmax_star(13, 792), 'at q=13 m=792')
for q in ppowers(300):
    check(kmax_star(q, q*q + 1) >= 2*q + 1, '(*) k<=2q+1 q=%d' % q)
print('   (*) holds for k <= 2q+1, m = q^2+1, every prime power q <= 300')

# 3. Theorem 2.1 on all labelled regular tournaments with 3, 5, 7 levels, every typing
def reg_tournaments(L):
    k = (L - 1)//2
    pairs = list(itertools.combinations(range(L), 2))
    res = []
    outd = [0]*L
    arcs = []
    def rec(i):
        if i == len(pairs):
            res.append(list(arcs)); return
        u, v = pairs[i]
        # remaining pairs involving u after this one
        for (x, y) in ((u, v), (v, u)):
            if outd[x] < k:
                outd[x] += 1; arcs.append((x, y))
                # prune: every vertex must still be able to reach out-degree k
                okp = True
                rec(i + 1)
                arcs.pop(); outd[x] -= 1
    rec(0)
    return [a for a in res if all(sum(1 for (x, y) in a if x == z) == k for z in range(L))]

for L in (3, 5, 7):
    k = (L - 1)//2; a = k//2
    tours = reg_tournaments(L)
    viol = 0
    best_tot = {}
    for arcs in tours:
        for bits in range(2**L):
            T = ''.join('H' if bits >> j & 1 else 'D' for j in range(L))
            f, g = fcount(T, arcs)
            # (a)
            if not (min(f) <= a and min(g) <= a): viol += 1
            if k % 2 == 0:
                if all(f[j] >= a for j in range(L)) and all(f[j] >= a + 1 for j in range(L) if T[j] == 'D'): viol += 1
                if all(g[j] >= a for j in range(L)) and all(g[j] >= a + 1 for j in range(L) if T[j] == 'H'): viol += 1
            else:
                if all(f[j] >= a + 1 for j in range(L) if T[j] == 'D') and all(g[j] >= a + 1 for j in range(L) if T[j] == 'H'): viol += 1
            for q, m in ((11, 768), (13, 792), (16, 257), (11, 122), (101, 101**2 + 1)):
                al, be = slots(T, arcs, P(q), Lam(q), m)
                key = (q, m)
                best_tot[key] = max(best_tot.get(key, (0, 0, 0)), (min(al) + min(be), min(al), min(be)))
    print('3. %d levels: %d labelled regular tournaments x %d typings, violations of Theorem 2.1 (a)-(c): %d' % (L, len(tours), 2**L, viol))
    check(viol == 0, 'Thm 2.1 L=%d' % L)
    for (q, m), (tot, ma, mb) in sorted(best_tot.items()):
        al, be = slots(alt(k), rot(L), P(q), Lam(q), m)
        check(tot == min(al) + min(be), 'alternating optimal L=%d q=%d m=%d' % (L, q, m))
        print('   q=%d m=%d: best min(alpha)+min(beta) over all = %d, alternating layout = %d' % (q, m, tot, min(al) + min(be)))

# 4. random regular tournaments on 9..15 levels (random rotations of arcs via 3-cycle reversals), random typings
random.seed(1)
for L in (9, 11, 13, 15):
    k = (L - 1)//2; a = k//2
    arcs = set(rot(L)); viol = 0; trials = 0
    adj = {(i, j) for (i, j) in arcs}
    for it in range(20000):
        # reverse a random directed 3-cycle (keeps regularity)
        x, y, z = random.sample(range(L), 3)
        if (x, y) in adj and (y, z) in adj and (z, x) in adj:
            adj -= {(x, y), (y, z), (z, x)}; adj |= {(y, x), (z, y), (x, z)}
        if it % 20 == 0:
            for _ in range(5):
                T = ''.join(random.choice('HD') for _ in range(L))
                f, g = fcount(T, adj); trials += 1
                if not (min(f) <= a and min(g) <= a): viol += 1
                if k % 2 == 0:
                    if all(f[j] >= a for j in range(L)) and all(f[j] >= a + 1 for j in range(L) if T[j] == 'D'): viol += 1
                else:
                    if all(f[j] >= a + 1 for j in range(L) if T[j] == 'D') and all(g[j] >= a + 1 for j in range(L) if T[j] == 'H'): viol += 1
    print('4. %d levels: %d random (tournament, typing) pairs, violations: %d' % (L, trials, viol))
    check(viol == 0, 'random L=%d' % L)

# 5. the build layouts of the table in Section 2 (symbolic: count P, Lam, m per level)
def sym(T):
    L = len(T); A = rot(L)
    al = [dict(P=0, L=0, m=0) for _ in range(L)]; be = [dict(P=0, L=0, m=0) for _ in range(L)]
    for (i, j) in A:
        key = ('P' if T[i] == 'H' else 'L') if T[i] != T[j] else 'm'
        al[i][key] += 1; be[j][key] += 1
    fmt = lambda d: '+'.join(('%d%s' % (d[x], {'P': 'P', 'L': 'Λ', 'm': 'm'}[x])).lstrip('1') if d[x] > 1 else {'P': 'P', 'L': 'Λ', 'm': 'm'}[x] for x in ('P', 'L', 'm') if d[x])
    return [fmt(d) for d in al], [fmt(d) for d in be]
for T in ('HDHDH', 'HHDHHDD', 'HHDHDHDHD'):
    al, be = sym(T)
    print('5.', T, 'alpha:', ', '.join(al), '| beta:', ', '.join(be))
# HHDHDHDHD is a rotation of the alternating typing for k = 4
check(any(alt(4)[r:] + alt(4)[:r] == 'HHDHDHDHD' for r in range(9)), 'rotation')

# 6. closed forms F_k (Corollary 3.2) against the slot formulas, all prime powers q <= 200, k = 1..q-1
def Fk(q, k):
    base = 2*(2*k + 1)*N(q)
    if k % 2 == 0: return base + k*(q**4 + 2*q**2 + q + 1)
    return base + (k - 1)//2*(2*q**4 + q**3 + q**2 + 2*q + 1) + (k + 1)*(q**2 + 1)
cnt = 0
for q in ppowers(200):
    for k in range(1, q):
        al, be = slots(alt(k), rot(2*k + 1), P(q), Lam(q), q*q + 1)
        check(Fk(q, k) == 2*(2*k + 1)*N(q) + min(al) + min(be), 'F_k q=%d k=%d' % (q, k)); cnt += 1
for q in range(2, 300):
    check(Fk(q, 2) == 10*N(q) + 2*q**4 + 4*q**2 + 2*q + 2, 'F2'); check(Fk(q, 3) == 14*N(q) + 2*q**4 + q**3 + 5*q**2 + 2*q + 5, 'F3')
    check(Fk(q, 4) == 18*N(q) + 4*q**4 + 8*q**2 + 4*q + 4, 'F4')
print('6. F_k(q) closed form = slot formula for %d pairs (q <= 200 prime power, 1 <= k <= q-1); F_2, F_3, F_4 expansions ok' % cnt)
print('ALL OK' if ok_all else 'SOME CHECK FAILED')
