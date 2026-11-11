#!/usr/bin/env python3
"""Referee's own search (written independently of hubopt.py) for hub graphs that are sums (Lemma 4.2) of blown-up
hexagons (Lemma 4.1) and at most one pendant-tree part on PG(2,s) (Lemma 4.3, last), for the (q, k) below the note's
thresholds q_k.  Objective as in the note: the largest K1 + K2 with K1 <= K_B, K2 <= K_A.  Prints our value next to
the note's (from certs.json, made by certs.py from hubopt.out)."""
import json, sys
from functools import lru_cache
def is_pp(n):
    if n < 2: return False
    for p in range(2, int(n**0.5) + 1):
        if n % p == 0:
            while n % p == 0: n //= p
            return n == 1
    return True
def K0(s): return (s + 1)*(s**4 + s**2 + 1)
def slots(q, k):
    m = q*q + 1; P = (q + 1)*(q**3 + 1); Lam = q**4 + q**2 + q; a = k//2
    if k % 2 == 0: return a*(Lam + m), a*(Lam + m)
    return a*P + (a + 1)*m, a*Lam + (a + 1)*m
PP = [s for s in range(2, 300) if is_pp(s)]

def tree_max(b):
    """largest per-colour size of a Lemma 4.3 part with own degree <= b, both colours equal (and the set of
    achievable (X, Y) is an interval-like region; we use the symmetric maximum and the minimum n)."""
    best = None
    for s in PP:
        if s + 1 > b: break
        n = s*s + s + 1; t = b - s - 1; u = b - 1
        hi = n + n*t + n*t*u
        if best is None or hi > best[1]: best = (n, hi, s)
    return best

def tree_feasible(s, b, X, Y):
    """exact: n + c_L + g_P = X, n + c_P + g_L = Y with 0 <= c_P, c_L <= n t, 0 <= g_P <= u c_P, 0 <= g_L <= u c_L
    (Lemma 4.3).  Raising c_P up to min(nt, Y - n) and c_L up to min(nt, X - n) only relaxes the conditions, so it is
    enough to test those values."""
    n = s*s + s + 1; t = b - s - 1; u = b - 1; nt = n*t
    x, y = X - n, Y - n
    if x < 0 or y < 0: return False
    cP, cL = min(nt, y), min(nt, x)
    return x <= cL + u*cP and y <= cP + u*cL

def assign_tree(parts, tree, T1, T2):
    """blow-up parts (lo, hi) filled first; the tree (s, b) takes what is left, reduced until Lemma 4.3 allows it"""
    s, b = tree; n = s*s + s + 1
    lo = sum(p[0] for p in parts); hi = sum(p[1] for p in parts)
    X = T1 - min(hi, T1 - n); Y = T2 - min(hi, T2 - n)
    mins = min([p[0] for p in parts]) if parts else 10**18
    X = min(X, mins); Y = min(Y, mins)
    # largest feasible sizes below the caps (see tree_feasible): x <= nt + u min(nt, y), y <= nt + u min(nt, x)
    t_ = b - s - 1; u_ = b - 1; nt_ = n*t_
    x, y = X - n, Y - n
    if x >= 0 and y >= 0:
        for _ in range(3):
            x = min(x, nt_ + u_*min(nt_, y)); y = min(y, nt_ + u_*min(nt_, x))
        X, Y = n + x, n + y
    if not (X >= n and Y >= n and tree_feasible(s, b, X, Y)): return None
    if X < n or Y < n: return None
    a = assign(parts + [(X, X)], T1, T2) if parts else None
    # assign() fills in order; force the tree sizes exactly
    res = []
    for (T, Z) in ((T1, X), (T2, Y)):
        if lo + Z > T: return None
        rem = T - Z - lo; x = [p[0] for p in parts]
        for i in range(len(parts)):
            add = min(parts[i][1] - parts[i][0], rem); x[i] += add; rem -= add
        res.append(x + [Z])
    A, B = res
    for i in range(len(A)):
        for j in range(i + 1, len(A)):
            if A[j] > B[i] or B[j] > A[i]: return None
    return sum(A), sum(B), A, B

def assign(parts, T1, T2):
    """parts: list of (lo, hi) per part (blow-ups first, in the given order); choose sizes with sums <= targets,
    maximal, and the order condition |A_j| <= |B_i|, |B_j| <= |A_i| (i < j).  Greedy: fill in order."""
    res = []
    for T in (T1, T2):
        lo = [p[0] for p in parts]; hi = [p[1] for p in parts]
        if sum(lo) > T: return None
        rem = T - sum(lo); x = list(lo)
        for i in range(len(parts)):
            add = min(hi[i] - lo[i], rem); x[i] += add; rem -= add
        res.append(x)
    A, B = res
    for i in range(len(parts)):
        for j in range(i + 1, len(parts)):
            if A[j] > B[i] or B[j] > A[i]: return None
    return sum(A), sum(B), A, B

def search(q, k, RMAX=10):
    T1, T2 = slots(q, k); d = q - k
    best = (0, None)
    for r in range(1, RMAX + 1):
        b = d - (r - 1)
        if b < 2: break
        types = sorted({(s, c) for s in PP if s + 1 <= b for c in range(1, b//(s + 1) + 1)},
                       key=lambda t: (-K0(t[0]), -t[1]))
        tr = tree_max(b)
        sufmax = [0]*(len(types) + 1)
        for i in range(len(types) - 1, -1, -1): sufmax[i] = max(sufmax[i + 1], types[i][1]*K0(types[i][0]))
        for with_tree in (False, True):
            nc = r - 1 if with_tree else r
            if with_tree and tr is None: continue
            trs = [None]
            def rec(start, chosen, lo):
                nonlocal best
                if len(chosen) == nc:
                    parts = [(K0(s), c*K0(s)) for (s, c) in chosen]
                    if with_tree:
                        a = None
                        for s3 in PP:            # every plane order that fits the part's own degree
                            if s3 + 1 > b: break
                            a3 = assign_tree(parts, (s3, b), T1, T2)
                            if a3 and (a is None or a3[0] + a3[1] > a[0] + a[1]): a = a3; trs[0] = s3
                    else:
                        a = assign(parts, T1, T2)
                    if a and a[0] + a[1] > best[0]:
                        best = (a[0] + a[1], (a[0], a[1], chosen, with_tree and trs[0]))
                    return
                for i in range(start, len(types)):
                    s, c = types[i]
                    if lo + K0(s) > min(T1, T2): continue
                    # bound: remaining parts at most this type's hi
                    left = nc - len(chosen)
                    ub = sum(c2*K0(s2) for (s2, c2) in chosen) + left*sufmax[i] + (tr[1] if with_tree else 0)
                    if 2*ub < best[0]: break
                    rec(i, chosen + [(s, c)], lo + K0(s))
            rec(0, [], 0)
            if best[0] == T1 + T2: return best, (T1, T2)
    return best, (T1, T2)

note = {tuple(map(int, kq.split(','))): v for kq, v in json.load(open('certs.json')).items()}
qk = {2: 16, 3: 23, 4: 23, 5: 29, 6: 23, 7: 31, 8: 29, 9: 37, 10: 32, 11: 43, 12: 41}
diff = 0
for k in range(2, 13):
    for q in range(k + 3, qk[k]):
        if not is_pp(q): continue
        (tot, info), (T1, T2) = search(q, k)
        n = note.get((k, q))
        ntot = (n[1] + n[2]) if n and n[0] != 'none' else 0
        flag = '' if tot == ntot else ('  <-- referee search larger' if tot > ntot else '  <-- note larger')
        if tot != ntot: diff += 1
        full = 'FULL' if tot == T1 + T2 else 'partial'
        print('k=%2d q=%3d slots=(%d,%d) referee %s K1+K2=%d %s | note %d%s' % (k, q, T1, T2, full, tot,
              '' if info is None else '%s%s' % ('+'.join('H(%d)x%d' % sc for sc in info[2]), ' + tree PG(2,%d)' % info[3] if info[3] else ''), ntot, flag), flush=True)
print('pairs where the two searches differ:', diff)
