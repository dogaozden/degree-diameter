# Random cubic bipartite bases on A=[0,h), B=[h,2h); writes "2h" then 3h edge lines "a b" (a in A, b in B).
import random, sys, os
def gen(h, rng):
    while True:
        A = [a for a in range(h) for _ in range(3)]
        B = [h + b for b in range(h) for _ in range(3)]
        rng.shuffle(B)
        edges = list(zip(A, B))
        # connectivity
        adj = {v: [] for v in range(2*h)}
        for a, b in edges:
            adj[a].append(b); adj[b].append(a)
        seen = {0}; st = [0]
        while st:
            x = st.pop()
            for y in adj[x]:
                if y not in seen: seen.add(y); st.append(y)
        if len(seen) == 2*h:
            return edges
def write(path, h, edges):
    with open(path, 'w') as f:
        f.write(f"{2*h}\n")
        for a, b in edges: f.write(f"{a} {b}\n")
if __name__ == "__main__":
    h = int(sys.argv[1]); k = int(sys.argv[2]); seed = int(sys.argv[3]); outdir = sys.argv[4]
    rng = random.Random(seed)
    os.makedirs(outdir, exist_ok=True)
    seen = set()
    for i in range(k):
        e = gen(h, rng)
        write(os.path.join(outdir, f"b{2*h}_{seed}_{i}.txt"), h, e)
