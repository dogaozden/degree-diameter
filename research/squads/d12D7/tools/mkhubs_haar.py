"""Hub layout for x5gen2 from a Haar graph (or any bipartite graph) used as the hub graph.

Usage: python3 mkhubs_haar.py HUBGRAPH.edges K OUT.hubs
HUBGRAPH.edges is a build_haar2.py edge list: first line 2N, then lines "a b" with a in [0, N) (side A) and b in
[N, 2N) (side B). Side A vertices become the N line-side hubs, side B the N point-side hubs. Hub j (on either side)
is owned by freed point j mod K, so N <= 2K is needed (each freed point has 2 free slots per level on each side).
Output format (x5gen2): "HL HP m", HL owner ids, HP owner ids, then m lines "j k".
"""
import sys

def main():
    src, K, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    with open(src) as f:
        nv = int(f.readline())
        N = nv // 2
        E = [tuple(map(int, l.split())) for l in f if l.strip()]
    assert nv == 2 * N and N <= 2 * K, (nv, K)
    for a, b in E:
        assert 0 <= a < N <= b < 2 * N, (a, b)
    with open(out, "w") as f:
        f.write(f"{N} {N} {len(E)}\n")
        f.write("\n".join(str(j % K) for j in range(N)) + "\n")
        f.write("\n".join(str(k % K) for k in range(N)) + "\n")
        f.write("\n".join(f"{a} {b - N}" for a, b in E) + "\n")
    print(f"N={N} K={K} hub-graph edges={len(E)} -> {out}")

if __name__ == "__main__":
    main()
