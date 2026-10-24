"""Delorme's product of a bipartite graph G with its side-swapped copy, and its polarity quotient.
Input: edge list of a connected bipartite G (first line n, then 'u v'); sides found by 2-colouring.
  product  P = G (x) Opp(G): vertices A x B and B x A, (x,y) ~ (x',y') iff x ~ x' and y ~ y' in G.
           bipartite, degree deg(x) deg(y), diameter = diam(G)            (BUILDINGS.md, Theorem 3)
  quotient Q: vertices A x B, (x,y) ~ (x',y') iff x ~ y' and y ~ x' (loops dropped); diameter <= diam(G) - 1.
usage: python3 delorme.py G.edges P.edges [Q.edges]"""
import sys
from collections import deque
with open(sys.argv[1]) as f:
    n = int(f.readline()); E = [tuple(map(int, l.split())) for l in f if l.strip()]
adj = [[] for _ in range(n)]
for a, b in E: adj[a].append(b); adj[b].append(a)
col = [-1] * n; col[0] = 0; dq = deque([0])
while dq:
    u = dq.popleft()
    for w in adj[u]:
        if col[w] < 0: col[w] = 1 - col[u]; dq.append(w)
        else: assert col[w] != col[u], "not bipartite"
assert min(col) >= 0, "not connected"
A = [v for v in range(n) if col[v] == 0]; B = [v for v in range(n) if col[v] == 1]
ia = {v: i for i, v in enumerate(A)}; ib = {v: i for i, v in enumerate(B)}
nA, nB = len(A), len(B)
# product: index (x in A, y in B) -> x_i*nB + y_j ; (x in B, y in A) -> nA*nB + x_j*nA + y_i
def pid_ab(x, y): return ia[x] * nB + ib[y]
def pid_ba(x, y): return nA * nB + ib[x] * nA + ia[y]
with open(sys.argv[2], 'w') as f:
    f.write(f"{2 * nA * nB}\n")
    for x in A:
        for y in B:
            u = pid_ab(x, y)
            for x2 in adj[x]:          # x2 in B
                for y2 in adj[y]:      # y2 in A
                    f.write(f"{u} {pid_ba(x2, y2)}\n")
print(f"G: {n} vertices (|A|={nA}, |B|={nB}); product: {2*nA*nB} vertices", file=sys.stderr)
if len(sys.argv) > 3:
    seen = 0
    with open(sys.argv[3], 'w') as f:
        f.write(f"{nA * nB}\n")
        for x in A:
            for y in B:
                u = ia[x] * nB + ib[y]
                for y2 in adj[x]:      # y2 in B : x ~ y2
                    for x2 in adj[y]:  # x2 in A : y ~ x2
                        v = ia[x2] * nB + ib[y2]
                        if u < v: f.write(f"{u} {v}\n")
    print(f"quotient: {nA*nB} vertices", file=sys.stderr)
