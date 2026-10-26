import random, sys
# union of 5 random perfect matchings between side A (0..h-1) and side B (h..2h-1) -> 5-regular bipartite multigraph
def make(h, seed, out):
    rnd = random.Random(seed)
    edges = []
    for _ in range(5):
        p = list(range(h)); rnd.shuffle(p)
        for i in range(h):
            edges.append((i, h + p[i]))
    with open(out, 'w') as f:
        f.write(f"{2*h} {len(edges)}\n")
        for u, v in edges: f.write(f"{u} {v}\n")
# K66 minus perfect matching (simple)
with open('base6_K66m.txt', 'w') as f:
    E = [(i, 6+j) for i in range(6) for j in range(6) if i != j]
    f.write(f"12 {len(E)}\n")
    for u, v in E: f.write(f"{u} {v}\n")
for s in range(1, 5): make(6, 100+s, f'base6_r{s}.txt')
for s in range(1, 3): make(8, 200+s, f'base8_r{s}.txt')
for s in range(1, 3): make(12, 300+s, f'base12_r{s}.txt')
