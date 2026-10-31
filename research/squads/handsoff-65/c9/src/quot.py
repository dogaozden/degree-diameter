# quot.py: quotient base of the Haar graph H(G,S) by a normal subgroup N (vl format, voltages in N).
# usage: quot.py GTABLE S NLINE BASE_OUT NTABLE_OUT
#   GTABLE: multiplication table file of G (m, then m rows; element 0 = identity)
#   S: comma list of table indices (the Haar connection set)
#   NLINE: line number (1-based) of N in normals342.txt (env NORM overrides the file; format "size name | idx idx ...")
#   BASE_OUT: vl base file ("b E", side bits, "u w volt" lines; side-0 vertices 0..k-1, side-1 k..2k-1)
#   NTABLE_OUT: multiplication table of N in its own indices (identity 0), for vl/tabu GROUP
# The base is gauge-normalised so that the tabu spanning tree (BFS from 0 in edge order) has identity voltages.
import sys, os
def main():
    gtab, S, nline, bout, ntout = sys.argv[1], [int(x) for x in sys.argv[2].split(',')], int(sys.argv[3]), sys.argv[4], sys.argv[5]
    normf = os.environ.get('NORM', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'normals342.txt'))
    with open(gtab) as f:
        m = int(f.readline()); T = [list(map(int, f.readline().split())) for _ in range(m)]
    inv = [0] * m
    for x in range(m):
        for y in range(m):
            if T[x][y] == 0: inv[x] = y; break
    with open(normf) as f:
        lines = [l for l in f if l.strip()]
    L = [int(x) for x in lines[nline - 1].split('|')[1].split()]
    L = [0] + sorted(x for x in L if x != 0)
    n = len(L); k = m // n
    assert n * k == m
    pos = {g: i for i, g in enumerate(L)}
    cos = [-1] * m; reps = []
    for x in range(m):
        if cos[x] < 0:
            c = len(reps); reps.append(x)
            for g in L: cos[T[g][x]] = c
    assert len(reps) == k
    NT = [[pos[T[L[i]][L[j]]] for j in range(n)] for i in range(n)]
    ninv = [0] * n
    for i in range(n):
        for j in range(n):
            if NT[i][j] == 0: ninv[i] = j
    edges = []
    for c, t in enumerate(reps):
        for s in S:
            x = T[t][s]; c1 = cos[x]
            v = T[x][inv[reps[c1]]]
            assert v in pos, "voltage not in N"
            edges.append((c, k + c1, pos[v]))
    B = 2 * k
    adj = [[] for _ in range(B)]
    for e, (u, w, v) in enumerate(edges):
        adj[u].append((w, e)); adj[w].append((u, e))
    seen = [False] * B; seen[0] = True; q = [0]; tree = set(); gam = [None] * B; gam[0] = 0
    qi = 0
    while qi < len(q):
        x = q[qi]; qi += 1
        for y, e in adj[x]:
            if not seen[y]:
                seen[y] = True; q.append(y); tree.add(e)
                u, w, v = edges[e]
                gam[y] = NT[ninv[v]][gam[x]] if x == u else NT[v][gam[x]]
    assert all(seen), "base not connected"
    newe = []
    for e, (u, w, v) in enumerate(edges):
        newe.append((u, w, NT[NT[ninv[gam[u]]][v]][gam[w]]))
    for e in tree: assert newe[e][2] == 0, "gauge failed"
    with open(bout, 'w') as f:
        f.write("%d %d\n" % (B, len(newe)))
        f.write(" ".join(["0"] * k + ["1"] * k) + "\n")
        for u, w, v in newe: f.write("%d %d %d\n" % (u, w, v))
    with open(ntout, 'w') as f:
        f.write("%d\n" % n)
        for i in range(n): f.write(" ".join(map(str, NT[i])) + "\n")
    print("base vertices %d (per side %d) edges %d N-order %d" % (B, k, len(newe), n))
main()
