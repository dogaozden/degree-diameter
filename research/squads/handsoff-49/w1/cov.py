# cov.py: fast Haar-cost evaluation from a group table (numpy).  Haar H(G,S), S contains e.
# A-side: uncovered x in G by radius-4 balls of U = {t^-1 s}; B-side: radius-4 balls of V = {s t^-1}.
import sys, numpy as np
def load(path):
    with open(path, 'rb') as f:
        N = int(np.fromfile(f, dtype=np.int32, count=1)[0])
        T = np.fromfile(f, dtype=np.uint16, count=N * N).reshape(N, N).astype(np.int32)
    return T
def inv_table(T):
    N = len(T); I = np.empty(N, dtype=np.int32)
    I[:] = np.argmax(T == 0, axis=1)   # row g: position of identity = inverse
    return I
def ball_uncov(T, gens, depth=4):
    N = len(T)
    reached = np.zeros(N, dtype=bool); reached[0] = True
    frontier = np.array([0])
    for _ in range(depth):
        if len(frontier) == 0: break
        # products g * x for x in frontier (left multiplication by gens) -- the ball is the same set for left/right
        nxt = np.unique(T[np.array(gens)[:, None], frontier[None, :]].ravel())
        nxt = nxt[~reached[nxt]]
        reached[nxt] = True
        frontier = nxt
    return int((~reached).sum())
def cost(T, I, S):
    # S = list of 4 element indices, S[0] = identity 0
    U = set(); V = set()
    for s in S:
        for t in S:
            U.add(T[I[t], s]); V.add(T[s, I[t]])
    U = [u for u in U if u != 0]; V = [v for v in V if v != 0]
    return ball_uncov(T, U), ball_uncov(T, V)
if __name__ == '__main__':
    T = load(sys.argv[1]); N = len(T); I = inv_table(T)
    samples = int(sys.argv[2]); rng = np.random.default_rng(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
    res = []
    for _ in range(samples):
        S = [0] + list(rng.choice(np.arange(1, N), 3, replace=False))
        a, b = cost(T, I, S)
        res.append((a + b, a, b, S))
    res.sort(key=lambda r: r[0])
    tot = np.array([r[0] for r in res])
    print("N", N, "samples", samples, "mean cost", tot.mean().round(2), "min", tot.min(), "hist", np.bincount(tot)[:20].tolist())
    print("best", res[0][:3], res[0][3])
