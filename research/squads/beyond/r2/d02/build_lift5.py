"""Build the 5-letter F4 route-chart lift from a chart file and a controller file (ctrl5 output).
usage: build_lift5.py CHART CTRL OUT_EDGES
Vertices: A-side (orbit i, g, x) -> (i*G+g)*256+x ; B-side (orbit j, h, y) -> N_A + (j*G+h)*256+y,
x, y in F4^4 encoded as base-4 digits. Edge (a_i,g,x) ~ (b_j, g+v, A_t x + lam*b_t), lam in F4, base edge (a_i,b_j) colour t."""
import sys
MUL = [[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]]
chart = []
for line in open(sys.argv[1]):
    v = list(map(int, line.split()))
    if not v: continue
    A = [v[r*4:(r+1)*4] for r in range(4)]
    b = v[16:20]
    chart.append((A, b))
assert len(chart) == 5
def mv(A, x):
    y = []
    for r in range(4):
        s = 0
        for c in range(4): s ^= MUL[A[r][c]][x[c]]
        y.append(s)
    return y
def enc(x): return x[0] + 4*x[1] + 16*x[2] + 64*x[3]
def dec(n): return [n & 3, (n >> 2) & 3, (n >> 4) & 3, (n >> 6) & 3]
lines = open(sys.argv[2]).read().split('\n')
k, G = map(int, lines[0].split())
edges = []
for ln in lines[1:]:
    p = ln.split()
    if len(p) != 4: continue
    edges.append(tuple(map(int, p)))
assert len(edges) == 5 * k
NA = k * G * 256
out = []
for (a, bb, t, v) in edges:
    A, bt = chart[t]
    for g in range(G):
        for xn in range(256):
            x = dec(xn)
            base = mv(A, x)
            for lam in range(4):
                y = [base[r] ^ MUL[lam][bt[r]] for r in range(4)]
                u = (a*G + g)*256 + xn
                w = NA + (bb*G + (g + v) % G)*256 + enc(y)
                out.append((u, w))
n = 2 * NA
with open(sys.argv[3], 'w') as f:
    f.write(f"{n}\n")
    f.write("\n".join(f"{u} {w}" for u, w in out))
    f.write("\n")
print("n", n, "edges", len(out), "m(per side)", k*G)
