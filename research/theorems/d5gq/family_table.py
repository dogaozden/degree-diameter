"""Values of the families of Section 10 of D5_QUADRANGLE.md at Delta = 4..16, against the 2013 table and the lab's records.
Explicit ingredients only (Theorem-level): q even: duality of W(q), ovoid of W(q) on every arc; q odd: typed rotational
layout over Q(4,q) with a = q^2+1 (ovoid), b = explicit partial ovoid of W(q) (Lemma 1.5: 3q-1 for q >= 5, 6 for q = 3),
c = 2 (Proposition 6.4); hub graphs from Lemma 9.1 (families F0, F1, F2, F3).  Output: family_table_out.txt"""
import itertools
from layouts import rotational

TABLE = {3: 56, 4: 160, 5: 336, 6: 684, 7: 1134, 8: 1710, 9: 2496, 10: 4000, 11: 5850, 12: 8200, 13: 11480,
         14: 14760, 15: 20496, 16: 27300}
LAB = {3: 56, 4: 162, 5: 354, 6: 684, 7: 1152, 8: 2048, 9: 2662, 10: 4800, 11: 7020, 12: 9840, 13: 11486, 14: 17568,
       15: 20736, 16: 33792}
PP = [2, 3, 4, 5, 7, 8, 9, 11, 13, 16]
N = lambda q: (q + 1) * (q * q + 1)


def hub_families(delta):
    """list of (name, (KB_lo, KB_hi), (KA_lo, KA_hi)) intervals; KB and KA chosen independently inside one family"""
    fam = []
    if delta >= 1:
        fam.append(('K_{x,y}', (1, delta), (1, delta)))
    for s in PP:
        if s + 1 <= delta:
            v = s * s + s + 1
            fam.append(('PG(2,%d)+pendants' % s, (v, v * (delta - s)), (v, v * (delta - s))))
            fam.append(('W(%d)+pendants' % s, (N(s), N(s) + (s + 1) * (delta - s - 1)), (N(s), N(s) + (s + 1) * (delta - s - 1))))
            for rr in range(1, delta - s):
                k = (2 * rr + 1) * N(s)
                fam.append(('level graph %d x W(%d)' % (2 * rr + 1, s), (k, k), (k, k)))
    return fam


def best_hubs(KB, KA, delta):
    best = (0, 0, 0, 'none')
    for name, (b0, b1), (a0, a1) in hub_families(delta):
        kb = min(KB, b1); ka = min(KA, a1)
        if kb >= b0 and ka >= a0 and kb + ka > best[0]:
            best = (kb + ka, kb, ka, name)
    return best


def slots_odd(q, r):
    """best rotational typed layout over Q(4,q), q odd, with explicit caps"""
    a = q * q + 1; b = 3 * q - 1 if q >= 5 else 6; c = 2
    L = 2 * r + 1
    if r == 0:
        return 0, 0, ''
    arcs = rotational(L, list(range(1, r + 1)))
    best = None
    for types in itertools.product('HD', repeat=L):
        out = [0] * L; inn = [0] * L
        for (u, v) in arcs:
            w = a if (types[u], types[v]) == ('H', 'D') else b if (types[u], types[v]) == ('D', 'H') else c
            out[u] += w; inn[v] += w
        key = (min(out) + min(inn), min(out), min(inn), ''.join(types))
        if best is None or key[0] > best[0]:
            best = key
    return best[1], best[2], best[3]


rows = []
for D in range(3, 17):
    cands = []
    for q in PP:
        r = D - q - 1
        if r < 0:
            continue
        base = (2 * r + 1) * 2 * N(q)
        if r == 0:
            cands.append((base, q, r, 'GQ incidence graph', 0, 0, ''))
            continue
        delta = q - r
        if q % 2 == 0:
            KB = KA = r * (q * q + 1); lay = 'all H, duality'
        elif r <= 6:
            KB, KA, lay = slots_odd(q, r)
        else:
            continue          # (2r+1 > 13 levels: not searched; these cells are far below the table anyway)
        tot, kb, ka, name = best_hubs(KB, KA, delta) if delta >= 1 else (0, 0, 0, 'none')
        cands.append((base + tot, q, r, lay, kb, ka, name))
    cands.sort(reverse=True)
    v, q, r, lay, kb, ka, name = cands[0]
    rows.append('(%2d,5)  table %6d  lab %6d   family %6d  (q=%d, r=%d, %s, K_B=%d, K_A=%d, hub graph %s)  %s' % (
        D, TABLE[D], LAB[D], v, q, r, lay, kb, ka, name,
        'beats table' if v > TABLE[D] else ''))
out = '\n'.join(rows)
print(out)
open('family_table_out.txt', 'w').write(out + '\n')
