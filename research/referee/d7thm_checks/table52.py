#!/usr/bin/env python3
"""Referee recomputation of the table of Section 5.2 and the random-hub-graph table of Section 4 of D7_THEOREMS.md.
'proved' = 2(2k+1)N(q) + K1 + K2 with the certificate of hubopt.out (validated by certs.py, stored in certs.json)."""
import json
def is_pp(n):
    if n < 2: return False
    for p in range(2, int(n**0.5) + 1):
        if n % p == 0:
            while n % p == 0: n //= p
            return n == 1
    return True
def N(q): return (q + 1)*(q**4 + q**2 + 1)
def slots(q, k):
    m = q*q + 1; P = (q + 1)*(q**3 + 1); Lam = q**4 + q**2 + q; a = k//2
    if k % 2 == 0: return a*(Lam + m), a*(Lam + m)
    return a*P + (a + 1)*m, a*Lam + (a + 1)*m
cert = {tuple(map(int, kq.split(','))): v for kq, v in json.load(open('certs.json')).items()}
qk = {2: 16, 3: 23, 4: 23, 5: 29, 6: 23, 7: 31, 8: 29, 9: 37, 10: 32, 11: 43, 12: 41}
hgcomp = {(11, 2), (13, 2), (16, 3), (17, 3), (19, 3), (19, 4)}     # random hub graphs found (Section 4 table)
note = {14: (1771560, (11, 2), 1801350, 'computer', 1797726), 15: (2480184, (11, 3), 2511429, 'open', 2503620),
        16: (4022340, (13, 2), 4080166, 'computer', 4079910), 17: (5631276, (13, 3), 5691471, 'open', 5686116),
        18: (7240212, (13, 4), 7355864, 'open', 7318644), 19: (11184810, (16, 2), 11316940, 'proof', 11316940),
        20: (15658734, (16, 3), 15795219, 'computer', 15791202), 21: (21120372, (17, 3), 21293811, 'computer', 21290219),
        22: (27154764, (17, 4), 27491232, 'open', 27476636), 23: (36591240, (19, 3), 36860589, 'computer', 36857870),
        24: (47045880, (19, 4), 47570132, 'computer', 47566386), 25: (57500520, (19, 5), 58038494, 'open', 58013214),
        26: (67955160, (19, 6), 68741538, 'open', 68663784)}
ok = True
for D in range(14, 27):
    cands = []
    for k in range(1, D):
        q = D - 1 - k
        if q < 2 or not is_pp(q) or k > q - 1: continue
        lev = 2*(2*k + 1)*N(q)
        KB, KA = slots(q, k); Fk = lev + KB + KA
        c = cert.get((k, q))
        prov = lev + (c[1] + c[2]) if c and c[0] != 'none' else None
        cands.append((lev, q, k, Fk, prov))
    lev_best = max(cands)
    prov_best = max((c[4] or 0, c[1], c[2]) for c in cands)
    F_best = max((c[3], c[1], c[2]) for c in cands)
    lev, q, k, Fk, prov = lev_best
    status = 'proof' if q >= qk.get(k, 10**9) else ('computer' if (q, k) in hgcomp else 'open')
    mine = (lev, (q, k), Fk, status, prov)
    eq = mine == note[D]
    ok &= eq
    print('(%d,7): level graphs %d at (q,k)=%s; F_k = %d; full slots: %s; proved %d; best proved over all (q,k): %d at %s; best F_k: %d at %s %s' % (
        D, lev, (q, k), Fk, status, prov, prov_best[0], prov_best[1:], F_best[0], F_best[1:], 'OK' if eq else 'DIFFERS from the note'))
    if prov_best[0] != prov: print('   note: a different (q,k) gives a larger proved value')
    if prov <= lev: ok = False; print('   proved value not above the level graphs')
print('Section 5.2 table reproduced:', ok)
# Section 4 random hub-graph table: K_B, K_A, M(delta)/K_B
def M(d): return 1 + d*(d - 1) + d*(d - 1)**3 + d*(d - 1)**5
rows = [(11, 2, 20.1), (13, 2, 38.4), (11, 3, 8.5), (13, 3, 19.2), (16, 3, 46.4), (17, 3, 58.7), (19, 3, 88.5), (11, 4, 1.9),
        (13, 4, 5.2), (16, 4, 14.7), (17, 4, 19.4), (19, 4, 30.9), (11, 5, 0.6), (13, 5, 2.2), (16, 5, 7.9), (17, 5, 11.0), (19, 5, 19.0)]
for (q, k, r) in rows:
    KB, KA = slots(q, k); rr = M(q - k)/KB
    print('  (%d,%d) delta=%d K_B=%d K_A=%d M/K_B=%.1f %s' % (q, k, q - k, KB, KA, rr, 'OK' if abs(rr - r) < 0.051 else 'DIFF (note %.1f)' % r))
