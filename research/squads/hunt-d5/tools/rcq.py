#!/usr/bin/env python3
"""Route-chart lift over F_q^4, q in {2,3,4,5} (hunt-d5): rcq.py q CTRL CHART OUT.edges
CTRL: "2m" then lines "u v c" (u in A = 0..m-1, v in B, colour c in {0,1,2}); lines "u v" without a colour are
coloured by peeling perfect matchings (Konig). CHART: chartq/chart3 lines "M<c> <16 digits> b<c> <4 digits>".
Lift: (u,x) ~ (v, M_c x + lam b_c), lam in F_q; vertex (w,x) = w*q^4 + x, x = sum x_i q^i. Check: apsp OUT 3q 5."""
import sys
q = int(sys.argv[1]); ctrl, chart, out = sys.argv[2:5]
if q == 4:
    ADD = [[a ^ b for b in range(4)] for a in range(4)]
    def gm(a, b):
        p = 0
        for i in range(2):
            if (b >> i) & 1: p ^= a << i
        if p & 4: p ^= 7
        return p
    MUL = [[gm(a, b) for b in range(4)] for a in range(4)]
else:
    ADD = [[(a + b) % q for b in range(q)] for a in range(q)]; MUL = [[a * b % q for b in range(q)] for a in range(q)]
M, B = {}, {}
for line in open(chart):
    t = line.split()
    if len(t) == 4 and t[0].startswith('M') and t[2].startswith('b'):
        c = int(t[0][1:]); M[c] = [[int(t[1][4 * i + j]) for j in range(4)] for i in range(4)]; B[c] = [int(ch) for ch in t[3]]
L = open(ctrl).read().split('\n'); n2 = int(L[0]); m = n2 // 2
E = []
for l in L[1:]:
    t = l.split()
    if not t: continue
    u, v = int(t[0]), int(t[1])
    if u >= m: u, v = v, u
    E.append([u, v, int(t[2]) if len(t) > 2 else None])
if any(e[2] is None for e in E):
    rem = [tuple(e[:2]) for e in E]; col = {}
    for c in range(3):
        adj = {u: [v for (a, v) in rem if a == u] for u in range(m)}; match = {}
        def aug(u, seen):
            for v in adj[u]:
                if v in seen: continue
                seen.add(v)
                if v not in match or aug(match[v], seen): match[v] = u; return True
            return False
        for u in range(m): assert aug(u, set())
        used = set((u, v) for v, u in match.items())
        for e in used: col[e] = c
        rem = [e for e in rem if e not in used]
    for e in E: e[2] = col[(e[0], e[1])]
F = q ** 4
def dec(k): return [k // q ** i % q for i in range(4)]
def enc(x): return sum(x[i] * q ** i for i in range(4))
with open(out, 'w') as f:
    f.write(f"{n2 * F}\n")
    for (u, v, c) in E:
        for k in range(F):
            x = dec(k); y0 = [0] * 4
            for i in range(4):
                s = 0
                for j in range(4): s = ADD[s][MUL[M[c][i][j]][x[j]]]
                y0[i] = s
            for lam in range(q):
                y = [ADD[y0[i]][MUL[lam][B[c][i]]] for i in range(4)]
                f.write(f"{u * F + k} {v * F + enc(y)}\n")
