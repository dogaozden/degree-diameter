"""Independent Python check of Haar graph H(G,S) from a group table: distance profile from (e,A)."""
import sys
import numpy as np

def load_bin(path):
    with open(path, 'rb') as f:
        N = int(np.frombuffer(f.read(4), dtype='<i4')[0])
        T = np.frombuffer(f.read(2 * N * N), dtype='<u2').reshape(N, N)
    return T

def haar_dist(T, S):
    """vertices: A-side g -> index g, B-side h -> index N+h. Edges (g,A)~(s g,B) for s in S."""
    N = len(T)
    Sarr = np.array(list(S), dtype=np.int64)
    inv = np.empty(N, dtype=np.int64)
    r, c = np.nonzero(T == 0)
    inv[r] = c
    dist = np.full(2 * N, -1, dtype=np.int64)
    dist[0] = 0
    frontier = np.array([0], dtype=np.int64)
    d = 0
    while frontier.size:
        d += 1
        A_part = frontier[frontier < N]
        B_part = frontier[frontier >= N] - N
        nb = []
        if A_part.size:
            nb.append((N + T[np.ix_(Sarr, A_part)].astype(np.int64)).ravel())
        if B_part.size:
            nb.append(T[np.ix_(inv[Sarr], B_part)].astype(np.int64).ravel())
        nb = np.unique(np.concatenate(nb)) if nb else np.array([], dtype=np.int64)
        nb = nb[dist[nb] < 0]
        dist[nb] = d
        frontier = nb
    return dist

if __name__ == '__main__':
    T = load_bin(sys.argv[1])
    rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    N = len(T)
    for trial in range(int(sys.argv[3]) if len(sys.argv) > 3 else 3):
        S = [0] + list(rng.choice(np.arange(1, N), 3, replace=False))
        d = haar_dist(T, S)
        A = d[:N]; B = d[N:]
        print("S", S, "unreachedA", int((A < 0).sum()), "unreachedB", int((B < 0).sum()),
              "A>8", int((A > 8).sum()), "B>8", int((B > 8).sum()), "maxA", int(A.max()), "maxB", int(B.max()))
