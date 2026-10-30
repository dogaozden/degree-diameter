import itertools, os
N = 6
def matrices():
    for a in itertools.product(range(N+1), repeat=3):
        if sum(a) != N: continue
        for b in itertools.product(range(N+1), repeat=3):
            if sum(b) != N: continue
            for c in itertools.product(range(N+1), repeat=3):
                if sum(c) != N: continue
                M = (a, b, c)
                if all(sum(M[i][j] for i in range(3)) == N for j in range(3)):
                    yield M
def canon(M):
    best = None
    for T in (False, True):
        A = [list(r) for r in M]
        if T:
            A = [[A[i][j] for i in range(3)] for j in range(3)]
        for p in itertools.permutations(range(3)):
            for q in itertools.permutations(range(3)):
                key = tuple(tuple(A[p[i]][q[j]] for j in range(3)) for i in range(3))
                if best is None or key < best: best = key
    return best
def connected(M):
    # bipartite: A_i ~ B_j if M[i][j] > 0
    seen = {('A',0)}; st = [('A',0)]
    while st:
        s, i = st.pop()
        if s == 'A':
            for j in range(3):
                if M[i][j] > 0 and ('B', j) not in seen:
                    seen.add(('B', j)); st.append(('B', j))
        else:
            for k in range(3):
                if M[k][i] > 0 and ('A', k) not in seen:
                    seen.add(('A', k)); st.append(('A', k))
    return len(seen) == 6
allm = list(matrices())
reps = {}
for M in allm:
    if not connected(M): continue
    reps.setdefault(canon(M), M)
print("all matrices", len(allm), "connected classes", len(reps))
os.makedirs('bases', exist_ok=True)
for idx, key in enumerate(sorted(reps)):
    M = key
    edges = []
    for i in range(3):
        for j in range(3):
            edges += [(i, 3 + j)] * M[i][j]
    name = f"bases/m{idx:02d}.txt"
    with open(name, 'w') as f:
        f.write(f"6 {len(edges)}\n0 0 0 1 1 1\n")
        for u, w in edges:
            f.write(f"{u} {w}\n")
    print(name, M)
