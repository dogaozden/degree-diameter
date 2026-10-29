#!/usr/bin/env python3
"""Check the formulas of D7_THEOREMS.md against the built graphs (job "conics" and job "conics-2"), and tabulate the
general bound of Corollary 3.2 for the cells (q+1+k, 7).

For each built graph: q, type string, freed-set sizes (P = (q+1)(q^3+1); Lam = q^4+q (lines meeting v + exact whiskers,
CONICS.md) or q^4+q^2+q (with S_0, conics2 Proposition 1); m = the non-friendly set), the hub counts used.  We compute
alpha_j, beta_j (Section 2 formulas), the slot minima, and n = 2 L N + K_A + K_B, and compare with the numbers printed
by the builders (make logs on branch claude/conics-2-diameter-7-ic0oat) and with n in the solution file names.
Output: cells.out"""
from hubcap_lib import slots

def N(q): return (q + 1) * (q ** 4 + q ** 2 + 1)
def alpha_beta(T, P, Lam, m):
    L = len(T); k = (L - 1) // 2
    al = [0] * L; be = [0] * L
    for j in range(L):
        for i in range(1, k + 1):
            j2 = (j + i) % L
            f = (P if T[j] == 'H' else Lam) if T[j] != T[j2] else m
            al[j] += f; be[j2] += f
    return al, be

# (cell, q, types, Lam variant, m, hubs (K_B, K_A), n claimed, builder's alpha, beta (from the make logs))
BUILT = [
    ('(14,7) conics', 11, 'HDHDH', 'whisk', 768, (15420, 15420), 1802400, None, None),
    ('(14,7)', 11, 'HDHDH', 'nu0', 768, (15541, 15541), 1802642,
     [16752, 15541, 16752, 29546, 16752], [15541, 31968, 15541, 16752, 15541]),
    ('(15,7) conics', 11, 'HHDHHDD', 'whisk', 768, (12180, 12180), 2504544, None, None),
    ('(15,7) PSL(2,31)', 11, 'HHDHHDD', 'nu0', 768, (14880, 14880), 2509944,
     [17520, 17520, 30314, 32736, 32736, 30314, 30314], [30314, 30314, 32736, 16309, 16309, 32736, 32736]),
    ('(15,7)', 11, 'HHDHHDD', 'nu0', 768, (16152, 16152), 2512488, None, None),
    ('(16,7) conics', 13, 'HDHDH', 'whisk', 792, (29366, 29366), 4081072, None, None),
    ('(16,7)', 13, 'HDHDH', 'nu0', 792, (29535, 29535), 4081410,
     [31564, 29535, 31564, 57486, 31564], [29535, 61544, 29535, 31564, 29535]),
    ('(17,7) whisk', 13, 'HHDHHDD', 'whisk', 792, (32356, 30158), 5693790,
     [32356, 32356, 57940, 62336, 62336, 57940, 57940], [57940, 57940, 62336, 30158, 30158, 62336, 62336]),
    ('(17,7)', 13, 'HHDHHDD', 'nu0', 792, (32356, 30327), 5693959,
     [32356, 32356, 58278, 62336, 62336, 58278, 58278], [58278, 58278, 62336, 30327, 30327, 62336, 62336]),
    ('(18,7) PSL(2,37)', 13, 'HHDHDHDHD', 'whisk', 792, (25308, 25308), 7290828,
     [63128, 63128, 58732, 63128, 58732, 63128, 86514, 63128, 86514], [58732, 58732, 93108, 58732, 93108, 58732, 63128, 58732, 63128]),
    ('(18,7)', 13, 'HHDHDHDHD', 'nu0', 792, (34440, 34440), 7309092,
     [63128, 63128, 59070, 63128, 59070, 63128, 87021, 63128, 87021], [59070, 59070, 93108, 59070, 93108, 59070, 63128, 59070, 63128]),
    ('(19,7) whisk', 16, 'HDHDH', 'whisk', 257, (65809, 65809), 11316428,
     [69906, 65809, 69906, 131104, 69906], [65809, 139298, 65809, 69906, 65809]),
    ('(19,7)', 16, 'HDHDH', 'nu0', 257, (66065, 66065), 11316940,
     [69906, 66065, 69906, 131616, 69906], [66065, 139298, 66065, 69906, 66065]),
    ('(20,7) whisk', 16, 'HHDHHDD', 'whisk', 257, (70163, 66066), 15794963,
     [70163, 70163, 131361, 139555, 139555, 131361, 131361], [131361, 131361, 139555, 66066, 66066, 139555, 139555]),
    ('(20,7)', 16, 'HHDHHDD', 'nu0', 257, (70163, 66322), 15795219,
     [70163, 70163, 131873, 139555, 139555, 131873, 131873], [131873, 131873, 139555, 66322, 66322, 139555, 139555]),
]

out = open('cells.out', 'w')
def say(*a):
    s = ' '.join(str(x) for x in a); print(s); out.write(s + '\n')

say('== 1. built graphs: formulas against the builders')
allok = True
for (name, q, T, var, m, (KB, KA), n, al_log, be_log) in BUILT:
    P = (q + 1) * (q ** 3 + 1)
    Lam = q ** 4 + q if var == 'whisk' else q ** 4 + q ** 2 + q
    al, be = alpha_beta(T, P, Lam, m)
    L = len(T); k = (L - 1) // 2
    ok = KB <= min(al) and KA <= min(be) and 2 * L * N(q) + KA + KB == n
    if al_log is not None:
        ok = ok and al == al_log and be == be_log
    allok &= ok
    tight = 'slots full' if (KB, KA) == (min(al), min(be)) else 'hub graph below the slots (%d, %d)' % (min(al), min(be))
    say('%-18s q=%2d %-9s Lam=%d m=%d: min alpha=%d min beta=%d; hubs %d+%d; 2LN+K = %d %s %d; %s%s' % (
        name, q, T, Lam, m, min(al), min(be), KB, KA, 2 * L * N(q) + KA + KB, '==' if 2 * L * N(q) + KA + KB == n else '!=', n,
        tight, '' if al_log is None else '; alpha/beta lists equal to the make log' if al == al_log and be == be_log else '; LIST MISMATCH'))
say('all consistent:', allok)

say('\n== 2. Corollary 3.2 with m = q^2+1: F_k(q) = 2(2k+1)N + K_A + K_B (alternating layout), cells (Delta, 7), Delta = q+1+k')
def F(q, k, m=None):
    KB, KA = slots(q, k, m)
    return 2 * (2 * k + 1) * N(q) + KA + KB, KB, KA
def closed(q, k):
    a = k // 2
    base = 2 * (2 * k + 1) * N(q)
    if k % 2 == 0:
        return base + k * (q ** 4 + 2 * q * q + q + 1)
    return base + a * (2 * q ** 4 + q ** 3 + q * q + 2 * q + 1) + (k + 1) * (q * q + 1)
for q in (11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37):
    for k in range(1, 7):
        f, KB, KA = F(q, k)
        assert f == closed(q, k)
say('closed forms of Corollary 3.2 agree with the slot formulas for q in {11,...,37}, k = 1..6')
for (q, k, mlab) in [(11, 2, 768), (11, 3, 768), (13, 2, 792), (13, 3, 792), (13, 4, 792), (16, 2, 257), (16, 3, 257)]:
    f, KB, KA = F(q, k); f2, KB2, KA2 = F(q, k, mlab)
    say('  (%d,7) q=%d k=%d: table 2(2k+1)N = %d; F_k(q) [m = q^2+1] = %d (K_B=%d, K_A=%d); with the lab set m=%d: %d (K_B=%d, K_A=%d)' % (
        q + 1 + k, q, k, 2 * (2 * k + 1) * N(q), f, KB, KA, mlab, f2, KB2, KA2))
