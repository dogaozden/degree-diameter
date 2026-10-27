# Part (A): psi(S_p) in PGL(2,q): size, closure under conjugation by h=psi(1+i+j+k), cycle type, order of h.
# Independent of lps_haar.c: own quaternion enumeration, own PGL normalisation.
import sys, itertools
from math import isqrt

def lps_set(p):
    S = []
    R = isqrt(p)
    for a0 in range(-R, R + 1):
        for a1 in range(-R, R + 1):
            for a2 in range(-R, R + 1):
                for a3 in range(-R, R + 1):
                    if a0*a0 + a1*a1 + a2*a2 + a3*a3 != p:
                        continue
                    if p % 4 == 1:
                        ok = a0 > 0 and a0 % 2 == 1 and a1 % 2 == 0 and a2 % 2 == 0 and a3 % 2 == 0
                    else:
                        ok = a0 % 2 == 0 and a1 % 2 == 1 and a2 % 2 == 1 and a3 % 2 == 1 and (a0 > 0 or (a0 == 0 and a1 > 0))
                    if ok:
                        S.append((a0, a1, a2, a3))
    return S

def xy_solutions(q):
    return [(x, y) for x in range(q) for y in range(q) if (x*x + y*y + 1) % q == 0]

def psi(quat, q, x, y):
    a0, a1, a2, a3 = quat
    return norm((a0 + a1*x + a3*y, -a1*y + a2 + a3*x, -a1*y - a2 + a3*x, a0 - a1*x - a3*y), q)

def norm(M, q):
    a, b, c, d = [t % q for t in M]
    lead = a if a else (b if b else (c if c else d))
    if lead == 0:
        return None  # singular
    t = pow(lead, q - 2, q)
    return (a*t % q, b*t % q, c*t % q, d*t % q)

def mul(X, Y, q):
    a, b, c, d = X; e, f, g, h = Y
    return ((a*e + b*g) % q, (a*f + b*h) % q, (c*e + d*g) % q, (c*f + d*h) % q)

def adj(X, q):
    a, b, c, d = X
    return ((d) % q, (-b) % q, (-c) % q, a % q)

def cycle_type(perm):
    n = len(perm); seen = [False]*n; ct = []
    for i in range(n):
        if not seen[i]:
            L = 0; j = i
            while not seen[j]:
                seen[j] = True; j = perm[j]; L += 1
            ct.append(L)
    return sorted(ct, reverse=True)

def predicted(p):
    if p == 3: return [3, 1]
    if p % 3 == 1: return sorted([3]*((p-1)//3) + [1, 1], reverse=True)
    return [3]*((p+1)//3)

def primes_upto(n):
    return [q for q in range(2, n+1) if all(q % d for d in range(2, isqrt(q)+1))]

def check(p, q, allsol=False):
    """return (list of failure strings, cycle type or None, order of h or None)"""
    fails = []
    sols = xy_solutions(q)
    if not sols:
        return ["no x,y"], None, None
    x, y = sols[0]
    S = lps_set(p)
    if len(S) != p + 1:
        fails.append(f"|S_p|={len(S)}")
    imgs = [psi(s, q, x, y) for s in S]
    if None in imgs:
        fails.append("singular image")
        return fails, None, None
    if len(set(imgs)) != len(imgs):
        fails.append(f"not distinct: {len(set(imgs))} of {len(imgs)}")
    h = psi((1, 1, 1, 1), q, x, y)
    if h is None:
        return fails + ["h singular"], None, None
    hi = norm(adj(h, q), q)
    # order of h in PGL
    P = h; order = 1
    ident = norm((1, 0, 0, 1), q)
    while P != ident and order <= 12:
        P = norm(mul(P, h, q), q); order += 1
    if P != ident:
        fails.append("h order > 12")
        order = None
    elif order != 3:
        fails.append(f"ord(h)={order}")
    # conjugation permutation
    idx = {g: i for i, g in enumerate(imgs)}
    perm = []
    for g in imgs:
        c = norm(mul(mul(h, g, q), hi, q), q)
        if c not in idx:
            fails.append("not closed under conj by h")
            return fails, None, order
        perm.append(idx[c])
    if len(set(perm)) != len(perm):
        fails.append("conj not a bijection")
    ct = cycle_type(perm)
    if ct != predicted(p):
        fails.append(f"cycle type {ct} != predicted {predicted(p)}")
    if allsol:
        for (x2, y2) in sols[1:]:
            im2 = [psi(s, q, x2, y2) for s in S]
            h2 = psi((1, 1, 1, 1), q, x2, y2)
            if None in im2 or h2 is None or len(set(im2)) != len(im2):
                fails.append(f"alt sol {(x2,y2)} degenerate"); continue
            h2i = norm(adj(h2, q), q); s2 = set(im2)
            if any(norm(mul(mul(h2, g, q), h2i, q), q) not in s2 for g in im2):
                fails.append(f"alt sol {(x2,y2)} not closed")
    return fails, ct, order

if __name__ == "__main__":
    allsol = "--allsol" in sys.argv
    ps = [3, 5, 7, 11, 13, 17, 19, 23, 29]
    total = 0
    per_part = {}
    rows = []
    for p in ps:
        for q in primes_upto(61):
            if q == p: continue
            fails, ct, order = check(p, q, allsol)
            rows.append((p, q, ct, order, fails))
            if fails:
                total += len(fails)
                print(f"FAIL p={p} q={q}: {fails}  ct={ct} ord={order}")
    ok = sum(1 for r in rows if not r[4])
    print(f"checked {len(rows)} (p,q) pairs; clean: {ok}; failure items: {total}")
    # summary of cycle types by p (for clean rows)
    for p in ps:
        cts = {tuple(r[2]) for r in rows if r[0] == p and r[2] is not None and not r[4]}
        print(f"p={p}: pred={predicted(p)} observed cycle types={sorted(cts)} clean q count={sum(1 for r in rows if r[0]==p and not r[4])}/{sum(1 for r in rows if r[0]==p)}")
    print("TOTAL_FAILURE_ITEMS", total)
