# connected quartic bipartite multigraphs with 3+3 vertices (3x3 nonneg int matrices, row/col sums 4), up to
# row/col permutations and transpose. Writes bases/b33_<i>.txt in flift base format ("6 12" then "u v" lines).
import itertools, os
p, s = 3, 4
def rows(n, t):
    if n == 1:
        yield (t,); return
    for a in range(t, -1, -1):
        for r in rows(n - 1, t - a):
            yield (a,) + r
def connected(M):
    seen, st = {0}, [0]
    while st:
        x = st.pop()
        nb = [p + j for j in range(p) if M[x][j]] if x < p else [i for i in range(p) if M[i][x - p]]
        for y in nb:
            if y not in seen: seen.add(y); st.append(y)
    return len(seen) == 2 * p
def canon(M):
    best = None
    for T in (M, tuple(zip(*M))):
        for rp in itertools.permutations(range(p)):
            for cp in itertools.permutations(range(p)):
                R = tuple(tuple(T[rp[i]][cp[j]] for j in range(p)) for i in range(p))
                if best is None or R < best: best = R
    return best
R = list(rows(p, s))
found = set()
for M in itertools.product(R, repeat=p):
    if all(sum(r) == s for r in M) and all(sum(M[i][j] for i in range(p)) == s for j in range(p)) and connected(M):
        found.add(canon(M))
os.makedirs("/home/user/degree-diameter/research/squads/own-small/r1/f1/bases", exist_ok=True)
for i, M in enumerate(sorted(found)):
    E = [(a, p + b) for a in range(p) for b in range(p) for _ in range(M[a][b])]
    with open(f"/home/user/degree-diameter/research/squads/own-small/r1/f1/bases/b33_{i}.txt", "w") as f:
        f.write(f"{2*p} {len(E)}\n" + "".join(f"{u} {v}\n" for u, v in E))
    print(i, M)
print("count", len(found))
