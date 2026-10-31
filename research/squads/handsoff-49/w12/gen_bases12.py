"""w12 base multigraphs: 4-regular connected bipartite multigraphs on h+h vertices.
h = 2, 3, 4: copied from w5's exhaustive classes (bases/mh{h}_*.txt).
h = 5, 7: random sampling (random 4 perfect matchings, multigraph), dedup by canonical sorted-row invariant.
Writes w12/bases/b{2h}_{tag}.txt in tabu format: first line n = 2h, then one edge 'u v' per line (u < h <= v).
Usage: python3 gen_bases12.py H COUNT SEED"""
import sys, os, random, itertools, shutil, glob
HERE = os.path.dirname(os.path.abspath(__file__))
W5 = os.path.join(HERE, "..", "w5", "bases")
OUT = os.path.join(HERE, "bases")
os.makedirs(OUT, exist_ok=True)

def write_base(path, h, edges):
    with open(path, "w") as f:
        f.write(f"{2*h}\n")
        for u, v in edges: f.write(f"{u} {v}\n")

def read_mh(path):
    L = open(path).read().split()
    b, m = int(L[0]), int(L[1])
    E = [(int(L[2+2*i]), int(L[3+2*i])) for i in range(m)]
    return b, E

def connected(h, edges):
    adj = {i: set() for i in range(2*h)}
    for u, v in edges: adj[u].add(v); adj[v].add(u)
    seen = {0}; st = [0]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in seen: seen.add(y); st.append(y)
    return len(seen) == 2*h

def invariant(h, edges):
    # 3 rounds of colour refinement on the multigraph (multiplicity-weighted), then the sorted colour multiset
    n = 2*h
    mult = {}
    for u, v in edges:
        mult[(u, v)] = mult.get((u, v), 0) + 1
        mult[(v, u)] = mult.get((v, u), 0) + 1
    col = [0]*n
    for _ in range(3):
        sig = []
        for x in range(n):
            nb = sorted((col[y], c) for (a, y), c in mult.items() if a == x)
            sig.append((col[x], tuple(nb)))
        ranks = {s: i for i, s in enumerate(sorted(set(sig)))}
        col = [ranks[s] for s in sig]
    return tuple(sorted(sig))

if __name__ == "__main__":
    H = int(sys.argv[1]); COUNT = int(sys.argv[2]); SEED = int(sys.argv[3])
    if H <= 4:
        files = sorted(glob.glob(os.path.join(W5, f"mh{H}_*.txt")))
        for f in files:
            b, E = read_mh(f)
            tag = os.path.basename(f)[:-4]
            write_base(os.path.join(OUT, f"b{2*H}_{tag}.txt"), H, E)
        print("copied", len(files), "bases for h =", H)
    else:
        rng = random.Random(SEED)
        seen = set(); got = []
        tries = 0
        while len(got) < COUNT and tries < 200000:
            tries += 1
            edges = []
            for _ in range(4):
                p = list(range(H)); rng.shuffle(p)
                edges += [(i, H + p[i]) for i in range(H)]
            if not connected(H, edges): continue
            key = invariant(H, edges)
            if key in seen: continue
            seen.add(key); got.append(edges)
        for idx, edges in enumerate(got):
            write_base(os.path.join(OUT, f"b{2*H}_r{SEED}_{idx}.txt"), H, edges)
        print("sampled", len(got), "bases for h =", H, "tries", tries)
