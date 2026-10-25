"""Item 1: is n tied to q?  For every record G = Q(q) x Z_n with Q a single SL/PSL/PGL(2,q): does n divide q-1, q+1,
or |Q|; is n prime; are all prime factors of n = 1 mod 3?  Split by orbit type (rand / orbit)."""
import json
from sympy import factorint, isprime
R = json.load(open('records.json'))
rows = []
for r in R:
    q, n = r['q'], r['n']
    if q is None or r['family'] != 'MatG' or n == 1: continue
    o = q * (q * q - 1)
    f = factorint(n)
    rows.append(dict(tag=r['tag'], q=q, n=n, orb=r['orbit'] != 'rand', qm=(q - 1) % n == 0, qp=(q + 1) % n == 0,
                     dQ=o % n == 0, prime=isprime(n), mod3=all(p % 3 == 1 for p in f)))
out = []
for orb in (False, True):
    S = [x for x in rows if x['orb'] == orb]
    out.append(f"{'orbit' if orb else 'random-S'} records with n > 1: {len(S)}; n | q-1: {sum(x['qm'] for x in S)}; "
               f"n | q+1: {sum(x['qp'] for x in S)}; n | |Q|: {sum(x['dQ'] for x in S)}; n prime: {sum(x['prime'] for x in S)}; "
               f"all primes of n = 1 mod 3: {sum(x['mod3'] for x in S)}")
out.append("pairs (q, n): " + ', '.join(f"({x['q']},{x['n']}{'o' if x['orb'] else ''})" for x in sorted(rows, key=lambda x: (x['q'], x['n']))))
open('nq_stats_out.txt', 'w').write('\n'.join(out) + '\n')
print('\n'.join(out))
