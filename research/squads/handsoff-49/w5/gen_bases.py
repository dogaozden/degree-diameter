"""Generate 4-regular bipartite base multigraphs for flift (format: 'b m' then m lines 'u v').
Vertices 0..h-1 on side A, h..2h-1 on side B (b = 2h). Usage: python3 gen_bases.py"""
import random, os, itertools
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bases")
os.makedirs(OUT, exist_ok=True)

def write(name, b, edges):
    with open(os.path.join(OUT, name), "w") as f:
        f.write(f"{b} {len(edges)}\n")
        for u, v in edges:
            f.write(f"{u} {v}\n")

def connected(b, edges):
    adj = {i: set() for i in range(b)}
    for u, v in edges:
        adj[u].add(v); adj[v].add(u)
    seen = {0}; st = [0]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y); st.append(y)
    return len(seen) == b

def bip_from_adj(h, A):  # A[i] = set of B-indices (0..h-1) adjacent to A-vertex i
    return [(i, h + j) for i in range(h) for j in sorted(A[i])]

# K_{h,h} minus a 4-regular complement... 4-regular simple bipartite on h+h: K_{h,h} minus (h-4)-regular bipartite
# b=10: K55 minus perfect matching
write("b10_k55m.txt", 10, bip_from_adj(5, [set(range(5)) - {i} for i in range(5)]))
# 4-cube
q4 = [(x, x ^ (1 << k)) for x in range(16) for k in range(4) if x < x ^ (1 << k)]
write("b16_q4.txt", 16, q4)
# complement of the Fano plane (7+7, girth 6)
fano = [{0,1,3},{1,2,4},{2,3,5},{3,4,6},{4,5,0},{5,6,1},{6,0,2}]
comp = [sorted(set(range(7)) - L) for L in fano]
write("b14_fanoc.txt", 14, bip_from_adj(7, [set(L) for L in comp]))
# bipartite circulants B(h; {0,1,2,3}) for h = 6,7,8
for h in (6, 7, 8):
    write(f"b{2*h}_circ{h}.txt", 2 * h, bip_from_adj(h, [{(i + s) % h for s in range(4)} for i in range(h)]))
# random 4-regular bipartite multigraphs (configuration model, parallel edges allowed up to mult 2)
def rand_multi(h, seed):
    rnd = random.Random(seed)
    while True:
        A = [i for i in range(h) for _ in range(4)]
        B = [j for j in range(h) for _ in range(4)]
        rnd.shuffle(B)
        edges = list(zip(A, B))
        cnt = {}
        for e in edges:
            cnt[e] = cnt.get(e, 0) + 1
        if max(cnt.values()) > 2:
            continue
        E = [(u, h + v) for (u, v) in edges]
        if connected(2 * h, E):
            return E

def rand_simple(h, seed):
    rnd = random.Random(seed)
    while True:
        A = [i for i in range(h) for _ in range(4)]
        B = [j for j in range(h) for _ in range(4)]
        rnd.shuffle(B)
        edges = list(zip(A, B))
        if len(set(edges)) != len(edges):
            continue
        E = [(u, h + v) for (u, v) in edges]
        if connected(2 * h, E):
            return E

if __name__ == "__main__":
    for h in (5, 6, 7, 8):
        for s in range(3):
            write(f"b{2*h}_rmulti{s}.txt", 2 * h, rand_multi(h, 100 * h + s))
            write(f"b{2*h}_rsimple{s}.txt", 2 * h, rand_simple(h, 1000 * h + s))
    print(sorted(os.listdir(OUT)))
