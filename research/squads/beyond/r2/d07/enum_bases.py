# Enumerate connected loopless bipartite cubic multigraphs on k+k vertices (k = 2,3,4); write base files.
import itertools, os
def rowsums_ok(M, k):
    return all(sum(r) == 3 for r in M) and all(sum(M[i][j] for i in range(k)) == 3 for j in range(k))
def connected(M, k):
    seen = {0}; st = [0]
    while st:
        v = st.pop()
        if v < k:
            nb = [k + j for j in range(k) if M[v][j] > 0]
        else:
            nb = [i for i in range(k) if M[i][v - k] > 0]
        for w in nb:
            if w not in seen:
                seen.add(w); st.append(w)
    return len(seen) == 2 * k
def canon(M, k):
    best = None
    for p in itertools.permutations(range(k)):
        for q in itertools.permutations(range(k)):
            t = tuple(M[p[i]][q[j]] for i in range(k) for j in range(k))
            if best is None or t < best: best = t
    return best
out = []
for k in (2, 3, 4):
    seen = set(); reps = []
    rows = [r for r in itertools.product(range(4), repeat=k) if sum(r) == 3]
    def rec(i, M, colsum):
        if i == k:
            if all(c == 3 for c in colsum):
                c = canon(M, k)
                if c not in seen and connected(M, k):
                    seen.add(c); reps.append([list(r) for r in M])
            return
        for r in rows:
            if all(colsum[j] + r[j] <= 3 for j in range(k)):
                rec(i + 1, M + [r], [colsum[j] + r[j] for j in range(k)])
    rec(0, [], [0] * k)
    for idx, M in enumerate(reps):
        edges = []
        for i in range(k):
            for j in range(k):
                edges += [(i, k + j)] * M[i][j]
        name = f"bases/bip{2*k}_{idx}.txt"
        with open(name, "w") as f:
            f.write(f"{2*k} {len(edges)}\n")
            for u, v in edges: f.write(f"{u} {v}\n")
        out.append((name, M))
        print(name, M)
