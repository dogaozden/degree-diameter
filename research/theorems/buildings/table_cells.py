"""Which cells of the bipartite degree-diameter table do building flag graphs touch, and how close do they get?

Families (BUILDINGS.md):
  F  flag graph Gamma of a finite thick building (all Lie types, generalized polygons with their known orders);
     sides E/P_I2 and E/P_I1, degrees P_I2 and P_I1, diameter h (Theorem 1)
  P  Delorme product Gamma (x) Opp(Gamma): regular of degree P_I1 * P_I2, order 2 |A| |B|, diameter h (Theorem 3)
  K  Kronecker product of two regular flag graphs with the same h: degree D1*D2, order n1*n2/2, diameter h
Every graph counts for every cell (Delta, D) with Delta >= its max degree and D >= its diameter.
Chamber counts: E = prod [d_i]_q (equal parameters); polar spaces of rank n with parameters (s,t):
E = prod_{i=0}^{n-1} [i+1]_s (1 + s^i t); generalized n-gons of order (s,t) closed forms; F4 with (q,q^2) (2E6)
by summing over W(F4) (weyl_dist.analyse).  Table: DS14v2 Table 4 (research/frontier/heuristic.py TABLE);
ours: research/frontier/TABLE.md arrows and research/RESULTS.md (largest value logged per cell)."""
import sys, re, itertools
sys.path.insert(0, '../../frontier'); sys.path.insert(0, '.')
from heuristic import TABLE, moore
from weyl_dist import analyse

def qi(d, q): return sum(q ** i for i in range(d))
def prime_powers(lim):
    out = []
    for n in range(2, lim + 1):
        p = next(p for p in range(2, n + 1) if n % p == 0)
        m = n
        while m % p == 0: m //= p
        if m == 1: out.append(n)
    return out
PP = prime_powers(300)

graphs = []   # (family, name, maxdeg, mindeg, D, order)
def add(fam, name, dA, dB, D, nA, nB):
    graphs.append((fam, name, max(dA, dB), min(dA, dB), D, nA + nB, dA, dB, nA, nB))

DEG = {'A': lambda n: list(range(2, n + 2)), 'B': lambda n: list(range(2, 2 * n + 1, 2)),
       'D': lambda n: list(range(2, 2 * n - 1, 2)) + [n], 'E6': [2, 5, 6, 8, 9, 12], 'E7': [2, 6, 8, 10, 12, 14, 18],
       'E8': [2, 8, 12, 14, 18, 20, 24, 30], 'F4': [2, 6, 8, 12], 'G2': [2, 6]}
def classes(t, n):
    """sizes of the colour classes and Coxeter number"""
    if t == 'A': return (n + 1) // 2, n // 2, n + 1
    if t == 'B': return (n + 1) // 2, n // 2, 2 * n
    if t == 'D': return (n - 2 + 1) // 2 + (0 if n % 2 == 0 else 2) if False else None
for q in PP:
    if q > 64: break
    # type A_n, n >= 2 (PG(n,q)); classes ceil(n/2), floor(n/2); h = n+1
    for n in range(2, 12):
        E = 1
        for d in DEG['A'](n): E *= qi(d, q)
        a, b = (n + 1) // 2, n // 2                      # |I1| (odd nodes), |I2|
        PI1, PI2 = (q + 1) ** a, (q + 1) ** b
        if min(PI1, PI2) > 300: break
        add('F', f"A{n}({q})", PI2, PI1, n + 1, E // PI2, E // PI1)
        add('P', f"A{n}({q})xOpp", PI1 * PI2, PI1 * PI2, n + 1, E * E // (PI1 * PI2), E * E // (PI1 * PI2))
    # polar spaces of rank n >= 2 with parameters (s,t): C_n; h = 2n; node n (special) in class of parity n
    polar = [('Sp/O', q, q), ('O-', q, q * q), ('U2n', q * q, q), ('U2n+1', q * q, q ** 3), ('GQ(q-1,q+1)', q - 1, q + 1),
             ('GQ(q+1,q-1)', q + 1, q - 1)]
    for nm, s, t in polar:
        for n in range(2, 8):
            if nm.startswith('GQ') and n > 2: break
            if s < 2 or t < 2: break
            E = 1
            for i in range(n): E *= qi(i + 1, s) * (1 + s ** i * t)
            odd_nodes = [k for k in range(1, n + 1) if k % 2 == 1]; even_nodes = [k for k in range(1, n + 1) if k % 2 == 0]
            par = lambda k: t if k == n else s
            PI1 = 1
            for k in odd_nodes: PI1 *= 1 + par(k)
            PI2 = 1
            for k in even_nodes: PI2 *= 1 + par(k)
            if min(PI1, PI2) > 300: break
            add('F', f"C{n}{nm}({q})" if not nm.startswith('GQ') else f"{nm}, q={q}", PI2, PI1, 2 * n, E // PI2, E // PI1)
            add('P', f"C{n}{nm}({q})xOpp" if not nm.startswith('GQ') else f"{nm}xOpp, q={q}", PI1 * PI2, PI1 * PI2, 2 * n,
                E * E // (PI1 * PI2), E * E // (PI1 * PI2))
    # D_n(q), n >= 4: path 1..n-2, leaves n-1, n at node n-2; h = 2n-2
    for n in range(4, 9):
        E = 1
        for d in DEG['D'](n): E *= qi(d, q)
        path = list(range(1, n - 1)); cls = {k: k % 2 for k in path}
        cls[n - 1] = cls[n] = 1 - cls[n - 2]
        a = sum(1 for k in cls if cls[k] == 1); b = n - a
        PI1, PI2 = (q + 1) ** a, (q + 1) ** b
        if min(PI1, PI2) > 300: break
        add('F', f"D{n}({q})", PI2, PI1, 2 * n - 2, E // PI2, E // PI1)
        add('P', f"D{n}({q})xOpp", PI1 * PI2, PI1 * PI2, 2 * n - 2, E * E // (PI1 * PI2), E * E // (PI1 * PI2))
    # exceptional, equal parameters
    for nm, h, a, b in (('E6', 12, 3, 3), ('E7', 18, 3, 4), ('E8', 30, 4, 4), ('F4', 12, 2, 2), ('G2', 6, 1, 1)):
        E = 1
        for d in DEG[nm]: E *= qi(d, q)
        PI1, PI2 = (q + 1) ** a, (q + 1) ** b
        if min(PI1, PI2) > 300: continue
        add('F', f"{nm}({q})", PI2, PI1, h, E // PI2, E // PI1)
        add('P', f"{nm}({q})xOpp", PI1 * PI2, PI1 * PI2, h, E * E // (PI1 * PI2), E * E // (PI1 * PI2))
    # generalized hexagons (q, q^3) = 3D4(q); octagons (q, q^2) = 2F4(q), q = 2^(2e+1)
    s, t = q, q ** 3
    if (1 + t) <= 300:
        P = (1 + s) * (1 + s * t + s * s * t * t); L = (1 + t) * (1 + s * t + s * s * t * t)
        add('F', f"GH({q},{q**3})", 1 + t, 1 + s, 6, P, L)
        add('P', f"GH({q},{q**3})xOpp", (1 + s) * (1 + t), (1 + s) * (1 + t), 6, P * L, P * L)
    if q in (2, 8, 32):
        s, t = q, q * q
        P = (1 + s) * (1 + s * t) * (1 + s * s * t * t); L = (1 + t) * (1 + s * t) * (1 + s * s * t * t)
        add('F', f"GO({q},{q*q})", 1 + t, 1 + s, 8, P, L)
        add('P', f"GO({q},{q*q})xOpp", (1 + s) * (1 + t), (1 + s) * (1 + t), 8, P * L, P * L)
# 2E6(q): F4 with parameters (q, q^2); classes {s1,s3} | {s2,s4} each with one q and one q^2 -> degree (1+q)(1+q^2)
C, I, cls, ncls, info, level = analyse('F', 4)
for q in PP:
    if (1 + q) * (1 + q * q) > 300: break
    E = 0
    for L in info.values(): E += q ** L[0] * (q * q) ** L[1]
    d = (1 + q) * (1 + q * q)
    add('F', f"2E6({q})", d, d, 12, E // d, E // d)
# Kronecker products of two regular flag graphs with the same diameter (q1 <= q2)
reg = [g for g in graphs if g[0] == 'F' and g[6] == g[7]]
for g1, g2 in itertools.combinations_with_replacement(reg, 2):
    if g1[4] == g2[4] and g1[2] * g2[2] <= 300:
        n = g1[5] * g2[5] // 2
        add('K', f"{g1[1]} (x) {g2[1]}", g1[2] * g2[2], g1[2] * g2[2], g1[4], n // 2, n - n // 2)

# ---- best known values: table + ours ----
ours = {}
for line in open('../../frontier/TABLE.md'):
    if line.startswith('| ') and line[2:4].strip().isdigit():
        cells = [c.strip() for c in line.strip().strip('|').split('|')]
        d = int(cells[0])
        for j, c in enumerate(cells[1:]):
            m = re.search(r'→ \*\*([\d,]+)\*\*', c)
            if m: ours[(d, j + 3)] = int(m.group(1).replace(',', ''))
for line in open('../../RESULTS.md'):
    for m in re.finditer(r'\((\d+),\s*(\d+)\)\s+(\d{1,3}(?:,\d{3})+|\d+)', line):
        d, D, n = int(m.group(1)), int(m.group(2)), int(m.group(3).replace(',', ''))
        if 3 <= d <= 16 and 3 <= D <= 10 and n > 10 and n > ours.get((d, D), 0): ours[(d, D)] = n

if __name__ == '__main__':
    print("A. Building-derived graphs that land IN the table range (max degree <= 16, diameter 3..10):")
    print("   family | graph | max deg | min deg | D | order | table | best known (ours) | order/table | order/Moore")
    for g in sorted(graphs, key=lambda g: (g[4], g[2], -g[5])):
        fam, name, dmax, dmin, D, n = g[:6]
        if dmax <= 16 and 3 <= D <= 10:
            tab = TABLE[dmax][D - 3] or 0; best = max(tab, ours.get((dmax, D), 0))
            print(f"   {fam} | {name} | {dmax} | {dmin} | {D} | {n:,} | {tab:,} | {best:,} | {n/tab:.3f} | {n/moore(dmax, D):.4f}"
                  f"{'  <-- above the 2013 table' if n > tab else ''}{'  <-- above best known' if n > best else ''}")
    print()
    print("B. Best building-derived value for every cell (graphs of max degree <= Delta and diameter <= D count):")
    print("   Delta \\ D | " + " | ".join(str(D) for D in range(3, 11)))
    for dl in range(3, 17):
        row = []
        for D in range(3, 11):
            cand = [g for g in graphs if g[2] <= dl and g[4] <= D]
            if not cand: row.append('-'); continue
            g = max(cand, key=lambda g: g[5])
            tab = TABLE[dl][D - 3] or 0; best = max(tab, ours.get((dl, D), 0))
            row.append(f"{g[5]:,} ({g[5]/best:.2f})" if best else f"{g[5]:,} (table n/a)")
        print(f"   {dl} | " + " | ".join(row))
    print("   (in brackets: building value / best known value, best known = max(2013 table, ours))")
