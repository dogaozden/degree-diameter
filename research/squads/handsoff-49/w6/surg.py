"""surg.py (w6): add two vertices to a valid bipartite 4-regular graph by surgery.
usage: surg.py BASE.edges OUT.edges SEED [MODE=4|3]
MODE 4: delete 4 pairwise disjoint edges (u_i in A, v_i in B); new a in A joins v_1..v_4, new b in B joins u_1..u_4.
MODE 3: delete 3 disjoint edges; a joins v_1..v_3 and b, b joins u_1..u_3 and a (edge ab).
Vertex colours come from a BFS 2-colouring. Prints the far count from score48 (D=9) of the result if SCORE=1 is set."""
import sys, random, collections

def load(path):
    with open(path) as f:
        n = int(f.readline())
        edges = [tuple(map(int, line.split())) for line in f if line.strip()]
    return n, edges

def colour(n, edges):
    adj = collections.defaultdict(list)
    for u, v in edges:
        adj[u].append(v); adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] < 0:
            col[s] = 0; q = [s]
            for x in q:
                for y in adj[x]:
                    if col[y] < 0:
                        col[y] = 1 - col[x]; q.append(y)
    return col

def surgery(n, edges, col, rng, mode):
    # orient every edge as (A-end, B-end)
    E = [(u, v) if col[u] == 0 else (v, u) for u, v in edges]
    k = 4 if mode == 4 else 3
    while True:
        idx = rng.sample(range(len(E)), k)
        used = set()
        ok = True
        for i in idx:
            u, v = E[i]
            if u in used or v in used:
                ok = False; break
            used.add(u); used.add(v)
        if ok:
            break
    removed = set(idx)
    new = [e for i, e in enumerate(E) if i not in removed]
    a, b = n, n + 1
    if mode == 4:
        for i in idx:
            u, v = E[i]
            new.append((a, v)); new.append((u, b))
    else:
        for i in idx:
            u, v = E[i]
            new.append((a, v)); new.append((u, b))
        new.append((a, b))
    return n + 2, new

def write(path, n, edges):
    with open(path, 'w') as f:
        f.write(f"{n}\n")
        for u, v in edges:
            f.write(f"{u} {v}\n")

if __name__ == '__main__':
    base, out, seed = sys.argv[1], sys.argv[2], int(sys.argv[3])
    mode = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    n, edges = load(base)
    col = colour(n, edges)
    rng = random.Random(seed)
    n2, e2 = surgery(n, edges, col, rng, mode)
    write(out, n2, e2)
    print(f"wrote {out} n={n2} m={len(e2)}")
