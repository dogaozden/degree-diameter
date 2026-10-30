# Base files: K_{k,k} minus a perfect matching (k-regular... degree k-1), written for vl.
import sys
k = int(sys.argv[1]); out = sys.argv[2]
b = 2 * k
edges = [(i, k + j) for i in range(k) for j in range(k) if i != j]
with open(out, "w") as f:
    f.write(f"{b} {len(edges)}\n")
    f.write(" ".join("0" if v < k else "1" for v in range(b)) + "\n")
    for u, w in edges:
        f.write(f"{u} {w}\n")
print(out, b, len(edges))
