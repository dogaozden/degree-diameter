"""Hub graph search for condition (HG) at D = 5: same-colour hubs within distance 4 in the whole graph.

D0[h, h'] = distance between hubs in the graph WITHOUT the hub graph Y (truncated: values > 4 stored as 9), from a BFS
of depth 4 out of every hub.  With Y, the hub-to-hub distance is the shortest path in the complete graph on the hubs
with weights min(D0, 1 for Y edges) (a path between two hubs splits at its hub visits into Y edges and level paths).
We anneal Y (bipartite B-hubs x A-hubs, max degree delta) to make every same-colour distance <= 4."""
import numpy as np, random


def hub_D0(n, edges, hubs):
    adj = [[] for _ in range(n)]
    for a, b in edges:
        adj[a].append(b); adj[b].append(a)
    idx = {h: i for i, h in enumerate(hubs)}
    K = len(hubs)
    D0 = np.full((K, K), 9, dtype=np.int16)
    for i, h in enumerate(hubs):
        dist = {h: 0}; fr = [h]
        for d in range(1, 5):
            nf = []
            for x in fr:
                for y in adj[x]:
                    if y not in dist:
                        dist[y] = d; nf.append(y)
            fr = nf
        for y, d in dist.items():
            j = idx.get(y)
            if j is not None:
                D0[i, j] = d
    return D0


def closure(W):
    D = W.copy()
    for _ in range(3):      # paths with up to 8 segments suffice for distances <= 4 (each segment >= 1)
        D = np.minimum(D, (D[:, :, None] + D[None, :, :]).min(axis=1))
    return D


def bad_pairs(D0, KB, KA, Y):
    W = D0.copy()
    for (h, g) in Y:
        W[h, KB + g] = W[KB + g, h] = 1
    D = closure(W)
    bb = (D[:KB, :KB] > 4).sum() // 2
    aa = (D[KB:, KB:] > 4).sum() // 2
    return int(bb + aa), D


def search(D0, KB, KA, delta, seed=0, iters=3000, verbose=False):
    rng = random.Random(seed)
    Eall = delta * min(KA, KB)
    stB = [h for h in range(KB) for _ in range(Eall // KB + (1 if h < Eall % KB else 0))]
    stA = [g for g in range(KA) for _ in range(Eall // KA + (1 if g < Eall % KA else 0))]
    while True:
        rng.shuffle(stA)
        Y = set(zip(stB, stA))
        if len(Y) == Eall: break
    Y = list(Y)
    cost, _ = bad_pairs(D0, KB, KA, Y)
    T = 1.0
    for it in range(iters):
        if cost == 0: break
        # double edge swap keeps all degrees
        i, j = rng.randrange(len(Y)), rng.randrange(len(Y))
        (h1, g1), (h2, g2) = Y[i], Y[j]
        if h1 == h2 or g1 == g2: continue
        S = set(Y)
        if (h1, g2) in S or (h2, g1) in S: continue
        Y2 = list(Y); Y2[i] = (h1, g2); Y2[j] = (h2, g1)
        c2, _ = bad_pairs(D0, KB, KA, Y2)
        if c2 <= cost or rng.random() < np.exp((cost - c2) / T):
            Y, cost = Y2, c2
        T = max(0.05, T * 0.999)
        if verbose and it % 200 == 0: print('  hubopt it', it, 'bad', cost)
    return Y, cost
