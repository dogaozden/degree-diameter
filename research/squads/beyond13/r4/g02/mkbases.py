# Build named cubic bipartite LCF bases (girth check), write lift.c format: "nverts" then "u v" (u in A=[0,h), v in B=[h,2h)).
import sys
from collections import deque
def lcf(L, reps):
    n = len(L) * reps
    ch = {}
    for i in range(n):
        s = L[i % len(L)]
        j = (i + s) % n
        ch.setdefault(i, set()).add(j); ch.setdefault(j, set()).add(i)
    E = set()
    for i in range(n):
        E.add(tuple(sorted((i, (i + 1) % n))))
    for i in range(n):
        for j in ch[i]:
            E.add(tuple(sorted((i, j))))
    return n, sorted(E)
def check(n, E):
    adj = {i: [] for i in range(n)}
    for a, b in E: adj[a].append(b); adj[b].append(a)
    assert all(len(adj[i]) == 3 for i in range(n)), "not cubic"
    col = {0: 0}; q = deque([0]); bip = True
    while q:
        x = q.popleft()
        for y in adj[x]:
            if y not in col: col[y] = 1 - col[x]; q.append(y)
            elif col[y] == col[x]: bip = False
    girth = 10**9
    for s in range(n):
        d = {s: 0}; par = {s: -1}; q = deque([s])
        while q:
            x = q.popleft()
            for y in adj[x]:
                if y not in d: d[y] = d[x] + 1; par[y] = x; q.append(y)
                elif par[x] != y: girth = min(girth, d[x] + d[y] + 1)
    return bip, girth, col
def write(name, n, E, col):
    A = [i for i in range(n) if col[i] == 0]; B = [i for i in range(n) if col[i] == 1]
    h = len(A); idx = {v: k for k, v in enumerate(A)}; idx.update({v: h + k for k, v in enumerate(B)})
    with open(name, "w") as f:
        f.write(f"{n}\n")
        for a, b in E:
            u, v = (a, b) if col[a] == 0 else (b, a)
            f.write(f"{idx[u]} {idx[v]}\n")
    print(name, "n", n, "h", h)
if __name__ == "__main__":
    specs = {
        "pappus18": ([5, 7, -7, 7, -7, -5], 3),
        "f26a26": ([-7, 7], 13),
        "dyck32": ([5, -9, 7, -7, 9, -5], 4),
        "tutte30": ([-13, -9, 7, -7, 9, 13], 5),
        "heawood14": ([5, -5], 7),
    }
    for name, (L, r) in specs.items():
        n, E = lcf(L, r)
        bip, girth, col = check(n, E)
        print(name, "edges", len(E), "bip", bip, "girth", girth)
        if bip and girth >= 6:
            write(f"/home/user/degree-diameter/research/squads/beyond13/r4/g02/{name}.txt", n, E, col)
    