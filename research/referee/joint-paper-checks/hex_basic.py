import sys, random, itertools
from collections import deque
from hexagon import Hex, write_edges
for q in map(int, sys.argv[1:]):
    H = Hex(q); F = H.F; N = H.N
    write_edges(f"H{q}.edges", 2 * N, H.incidence_edges())
    # lines through e0
    e0 = H.pid[(1, 0, 0, 0, 0, 0, 0)]
    through = [set(tuple(H.pts[i]) for i in H.lines[k]) for k in H.lines_on[e0]]
    ok_e0 = all(all(p[1] == p[2] == p[3] == p[4] == 0 for p in L) for L in through)
    # Lemma 2.4(c) on points from e0 and a few others: d<=4 iff perpendicular
    adjP = [[j for k in H.lines_on[i] for j in H.lines[k] if j != i] for i in range(N)]
    bad = 0
    for s in random.sample(range(N), 5) + [e0]:
        dist = {s: 0}; dq = deque([s])
        while dq:
            u = dq.popleft()
            for w in adjP[u]:
                if w not in dist: dist[w] = dist[u] + 1; dq.append(w)
        for j in range(N):
            perp = H.b(H.pts[s], H.pts[j]) == 0
            bad += ((dist[j] <= 2) != perp)   # point-graph distance <=2 means incidence distance <=4
    # Fact 2.3: (v,a,w) -> (Av, a, A^{-T} w) for random A in SL(3,q)
    M, A_, S_ = F.mul, F.add, F.sub
    def matmul(X, Y): return [[ (lambda r: r)(0) for _ in range(3)] for _ in range(3)]
    def mm(X, Y):
        Z = [[0]*3 for _ in range(3)]
        for i in range(3):
            for j in range(3):
                t = 0
                for k in range(3): t = A_[t][M[X[i][k]][Y[k][j]]]
                Z[i][j] = t
        return Z
    def det(X):
        t = 0
        for perm, sg in [((0,1,2),1),((1,2,0),1),((2,0,1),1),((0,2,1),-1),((2,1,0),-1),((1,0,2),-1)]:
            pr = M[M[X[0][perm[0]]][X[1][perm[1]]]][X[2][perm[2]]]
            t = A_[t][pr] if sg == 1 else S_[t][pr]
        return t
    def inv3(X):
        d = det(X); idt = F.inv[d]
        C = [[0]*3 for _ in range(3)]
        for i in range(3):
            for j in range(3):
                minor = [[X[r][c] for c in range(3) if c != j] for r in range(3) if r != i]
                m = S_[M[minor[0][0]][minor[1][1]]][M[minor[0][1]][minor[1][0]]]
                if (i + j) % 2: m = F.neg[m]
                C[j][i] = M[m][idt]
        return C
    okcol = True
    for trial in range(3):
        while True:
            Am = [[random.randrange(q) for _ in range(3)] for _ in range(3)]
            dd = det(Am)
            if dd: break
        # scale first row to get det 1
        idd = F.inv[dd]; Am[0] = [M[idd][t] for t in Am[0]]; assert det(Am) == 1
        Ai = inv3(Am); AiT = [[Ai[j][i] for j in range(3)] for i in range(3)]
        def img(x):
            v = x[0:3]; a = x[3]; w = x[4:7]
            Av = [A_[A_[M[Am[i][0]][v[0]]][M[Am[i][1]][v[1]]]][M[Am[i][2]][v[2]]] for i in range(3)]
            Bw = [A_[A_[M[AiT[i][0]][w[0]]][M[AiT[i][1]][w[1]]]][M[AiT[i][2]][w[2]]] for i in range(3)]
            return H.pid[H.norm(Av + [a] + Bw)]
        for L in H.lines:
            if frozenset(img(H.pts[i]) for i in L) not in H.lid: okcol = False; break
    print(f"q={q}: |P|=|L|={N}, each point on q+1 lines; lines through e0 in <e0,e5,e6>: {ok_e0};"
          f" Lemma 2.4(c) mismatches: {bad}; SL(3) map preserves lines: {okcol}")
