"""Independent check of a Haar graph H(G,S) for G = Z_m x|_r Z_k (element a + m*j, (a,j)(b,l) = (a + r^j b, j+l)).
Uses only python BFS on the 2N-vertex graph (edges (g,A) ~ (s g,B)), no table, no exh3/hx code.
usage: witness.py m k r "x,y,z" [edges_out] [must,...]
prints the cost (vertices of each side not within 8 of that side's root; cost 0 iff diameter <= 9 when the
graph is vertex-transitive, which holds here) and the must-coverage test."""
import sys, random
from collections import deque
m, k, r = map(int, sys.argv[1:4])
S = [0] + [int(t) for t in sys.argv[4].split(',')]
edges_out = sys.argv[5] if len(sys.argv) > 5 and sys.argv[5] != '-' else None
must = [int(t) for t in sys.argv[6].split(',')] if len(sys.argv) > 6 and sys.argv[6] else []
N = m * k
rp = [pow(r, j, m) for j in range(k)]
def mul(g, h):
    a, j = g % m, g // m
    b, l = h % m, h // m
    return (a + rp[j] * b) % m + m * ((j + l) % k)
# group law checks: r^k = 1 mod m, identity 0, associativity on random triples, closure by construction
assert pow(r, k, m) == 1 % m, "r^k != 1 mod m"
random.seed(1)
for _ in range(200000):
    a, b, c = (random.randrange(N) for _ in range(3))
    assert mul(mul(a, b), c) == mul(a, mul(b, c)), "associativity fails"
inv = [next(h for h in range(N) if mul(g, h) == 0) for g in range(N)]
assert len(set(S)) == 4 and all(0 <= s < N for s in S)
# adjacency: A-vertex g ~ B-vertex s*g (s in S), B-vertex h ~ A-vertex s^-1 * h
def bfs(root):
    d = [-1] * (2 * N); d[root] = 0; q = deque([root])
    while q:
        v = q.popleft()
        if d[v] >= 8:
            continue
        if v < N:
            nbrs = [N + mul(s, v) for s in S]
        else:
            nbrs = [mul(inv[s], v - N) for s in S]
            # (from a B-vertex, the A-neighbours are s^-1 h)
        for w in nbrs:
            if d[w] < 0:
                d[w] = d[v] + 1; q.append(w)
    return d
dA = bfs(0)      # root (e,A)
dB = bfs(N)      # root (e,B)
costA = sum(1 for g in range(N) if not (0 <= dA[g] <= 8))   # A-side vertices not within 8 of (e,A)
costB = sum(1 for g in range(N) if not (0 <= dB[N + g] <= 8))  # B-side vertices not within 8 of (e,B)
cost = costA + costB
ok_must = all((0 <= dA[g] <= 8) and (0 <= dB[N + g] <= 8) for g in must)
print(f"m={m} k={k} r={r} N={N} S={S} cost={cost} (A-side {costA}, B-side {costB}) must={must} must_ok={ok_must}")
# full-diameter cross-check from the two roots (edges of the graph: 4 per A-vertex, degree 4 each side)
if edges_out:
    with open(edges_out, 'w') as f:
        f.write(f"{2*N}\n")
        for s in S:
            for g in range(N):
                f.write(f"{g} {N + mul(s, g)}\n")
    print("wrote", edges_out)
