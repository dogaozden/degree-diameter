#!/usr/bin/env python3
"""Route-chart lift over F_3^4 (hunt-d5): rclift.py CTRL.edges CHART.txt OUT.edges
CTRL.edges: "2m" then lines "u v" (cubic bipartite controller; side A = 0..m-1, side B = m..2m-1).
CHART.txt: chart3 output lines "M<c> <16 digits> b<c> <4 digits>" (c = 0,1,2).
The controller is properly 3-edge-coloured (Konig, by repeated perfect matchings), colour c uses letter c.
Lift: (u,x) ~ (v, M_c x + lam b_c), lam in F_3, vertex (w,x) = w*81 + x (x = sum x_i 3^i). Then: apsp OUT.edges 9 5."""
import sys
def read_chart(fn):
    M, b = {}, {}
    for line in open(fn):
        t = line.split()
        if len(t) == 4 and t[0].startswith('M') and t[2].startswith('b'):
            c = int(t[0][1:]); M[c] = [[int(t[1][4*i+j]) for j in range(4)] for i in range(4)]; b[c] = [int(ch) for ch in t[3]]
    return M, b
def colour(m, edges):
    # proper 3-edge-colouring of a cubic bipartite graph: peel off perfect matchings (Hopcroft-Karp-lite / augmenting)
    rem = list(edges); col = {}
    for c in range(3):
        adj = {u: [] for u in range(m)}
        for (u, v) in rem: adj[u].append(v)
        match = {}
        def aug(u, seen):
            for v in adj[u]:
                if v in seen: continue
                seen.add(v)
                if v not in match or aug(match[v], seen): match[v] = u; return True
            return False
        for u in range(m):
            if not aug(u, set()): raise SystemExit("no perfect matching")
        used = set((u, v) for v, u in match.items())
        for e in used: col[e] = c
        rem = [e for e in rem if e not in used]
    return col
def enc(x): return x[0] + 3 * x[1] + 9 * x[2] + 27 * x[3]
def dec(k): return [k % 3, k // 3 % 3, k // 9 % 3, k // 27 % 3]
def main():
    ctrl, chart, out = sys.argv[1:4]
    lines = open(ctrl).read().split('\n'); n2 = int(lines[0]); m = n2 // 2
    edges = [tuple(map(int, l.split())) for l in lines[1:] if l.strip()]
    edges = [(u, v) if u < m else (v, u) for (u, v) in edges]
    assert len(edges) == 3 * m and len(set(edges)) == 3 * m, "controller must be simple and cubic"
    col = colour(m, edges)
    M, b = read_chart(chart)
    with open(out, 'w') as f:
        f.write(f"{n2 * 81}\n")
        for (u, v) in edges:
            c = col[(u, v)]
            for k in range(81):
                x = dec(k); y0 = [sum(M[c][i][j] * x[j] for j in range(4)) % 3 for i in range(4)]
                for lam in range(3):
                    y = [(y0[i] + lam * b[c][i]) % 3 for i in range(4)]
                    f.write(f"{u * 81 + k} {v * 81 + enc(y)}\n")
main()
