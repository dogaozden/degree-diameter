"""Hard-set analysis for Haar graphs H(G,S): vertices (g,A),(g,B); edges (g,A) ~ (s g,B). Far = distance > 8.
Usage: python3 hard.py G.bin SOL1 SOL2 ...   (SOL: lift solution files with lines 'e u v s')"""
import sys
from collections import Counter
import numpy as np

def load_table(path):
    with open(path, "rb") as f:
        N = int(np.fromfile(f, dtype=np.int32, count=1)[0])
        T = np.fromfile(f, dtype=np.uint16, count=N * N).reshape(N, N).astype(np.int64)
    return N, T

def inverses(N, T):
    inv = np.zeros(N, dtype=np.int64)
    for a in range(N):
        inv[a] = int(np.nonzero(T[a] == 0)[0][0])  # identity is index 0
    return inv

def read_S(path):
    S = []
    for line in open(path):
        p = line.split()
        if p and p[0] == "e":
            S.append(int(p[3]))
    return S

def far_sets(N, T, inv, S):
    """Return (far_from_A, far_from_B): lists of (side, g) far from source (e,A) and (e,B)."""
    # adjacency: A node g (index g) ~ B node s*g (index N+s*g); B node h ~ A node s^-1 * h
    n = 2 * N
    adj = [[] for _ in range(n)]
    for s in S:
        si = inv[s]
        for g in range(N):
            b = N + int(T[s, g])
            adj[g].append(b)
            adj[b].append(g)
    out = []
    for src in (0, N):
        dist = [-1] * n
        dist[src] = 0
        frontier = [src]
        d = 0
        while frontier:
            d += 1
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if dist[v] < 0:
                        dist[v] = d
                        nxt.append(v)
            frontier = nxt
        far = []
        for v in range(n):
            if dist[v] < 0 or dist[v] > 8:
                far.append(("A" if v < N else "B", v % N))
        out.append(far)
    return out

if __name__ == "__main__":
    N, T = load_table(sys.argv[1])
    inv = inverses(N, T)
    cnt = Counter()
    per_state = []
    for path in sys.argv[2:]:
        S = read_S(path)
        fa, fb = far_sets(N, T, inv, S)
        far = [("srcA",) + x for x in fa] + [("srcB",) + x for x in fb]
        cnt.update(set(far))
        per_state.append((path, S, len(fa) + len(fb)))
        print(path.split("/")[-1], "S=", S, "cost=", len(fa) + len(fb), "far_src_A=", len(fa), "far_src_B=", len(fb))
    m = len(sys.argv) - 2
    print("states", m, "distinct far labels", len(cnt))
    print("most frequent far labels (label count):")
    for lab, c in cnt.most_common(25):
        print(lab, c)
    # hist of frequencies
    hist = Counter(cnt.values())
    print("freq histogram", sorted(hist.items()))
