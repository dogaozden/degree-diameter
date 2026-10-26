import sys
# mkbase.py NAME "r1;r2;..." : biadjacency matrix rows (side A = 0..a-1, side B = a..a+b-1)
name, rows = sys.argv[1], [list(map(int, r.split(","))) for r in sys.argv[2].split(";")]
a, b = len(rows), len(rows[0])
assert all(sum(r) == 6 for r in rows) and all(sum(rows[i][j] for i in range(a)) == 6 for j in range(b))
edges = [(i, a + j) for i in range(a) for j in range(b) for _ in range(rows[i][j])]
with open(f"bases/{name}.txt", "w") as f:
    f.write(f"{a+b} {len(edges)}\n")
    for u, v in edges: f.write(f"{u} {v}\n")
print(name, a + b, len(edges))
