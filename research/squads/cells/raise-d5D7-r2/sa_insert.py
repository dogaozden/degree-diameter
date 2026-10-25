# sa_insert.py: annealing (non-symmetric) from the record graph plus two inserted vertices (3122 vertices, 5-regular,
# bipartite). Cost = number of ordered pairs at distance > 7 (packed-bit all-pairs reach sets). Moves: bipartite
# double-edge switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), which keep the graph 5-regular and bipartite.
# usage: python3 -I sa_insert.py SEED SECONDS TEMP0 OUTPREFIX
import sys, os, random, time, math
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import numpy as np
import r2sweep as R
from insert_exp import haar_nbrs, insert, matching_edges

POP = np.array([bin(i).count('1') for i in range(256)], dtype=np.int64)

def cost(nbr, D=7):
    V, d = nbr.shape
    P = (V + 7) // 8
    eye = np.zeros((V, V), dtype=bool); eye[np.arange(V), np.arange(V)] = True
    Rw = np.packbits(eye, axis=1)                       # V x P
    for _ in range(D):
        Rn = Rw.copy()
        for j in range(d): Rn |= Rw[nbr[:, j]]
        Rw = Rn
    return int(V * V - POP[Rw].sum())

def edge_switch(nbr, rng):
    """propose a double edge switch; returns (nbr_new, changed rows) or None."""
    V, d = nbr.shape; N = V // 2
    a1 = rng.randrange(N); j1 = rng.randrange(d); b1 = int(nbr[a1, j1])
    a2 = rng.randrange(N); j2 = rng.randrange(d); b2 = int(nbr[a2, j2])
    if a1 == a2 or b1 == b2: return None
    if (nbr[a1] == b2).any() or (nbr[a2] == b1).any(): return None
    new = nbr.copy()
    new[a1, j1] = b2; new[a2, j2] = b1
    k1 = int(np.where(new[b1] == a1)[0][0]); new[b1, k1] = a2
    k2 = int(np.where(new[b2] == a2)[0][0]); new[b2, k2] = a1
    return new

def check_full(nbr, D=7):
    """independent BFS check from every vertex (plain python), returns max eccentricity."""
    V = nbr.shape[0]; adj = [list(map(int, r)) for r in nbr]; worst = 0
    for s in range(V):
        dist = [-1] * V; dist[s] = 0; fr = [s]; lvl = 0
        while fr:
            lvl += 1; nf = []
            for x in fr:
                for y in adj[x]:
                    if dist[y] < 0: dist[y] = lvl; nf.append(y)
            fr = nf
        if min(dist) < 0: return None
        worst = max(worst, max(dist))
    return worst

if __name__ == '__main__':
    seed = int(sys.argv[1]); secs = float(sys.argv[2]); T0 = float(sys.argv[3]); out = sys.argv[4]
    rng = random.Random(seed)
    S = [0, 858, 14, 367, 698]
    M = R.build_group(['PGL25', 'Z13']); N = M.shape[0]
    nbr0 = haar_nbrs(M, S)
    best = None
    for _ in range(int(os.environ.get('INIT_TRIES', '6'))):
        nb = insert(nbr0, N, matching_edges(nbr0, N, rng))
        c = cost(nb)
        if best is None or c < best[0]: best = (c, nb)
    c, nbr = best
    print(f"start cost={c}", flush=True)
    t0 = time.time(); step = 0; bestc = c; acc = 0
    while time.time() - t0 < secs:
        step += 1
        T = T0 * (1 - (time.time() - t0) / secs) + 1e-3
        nn = edge_switch(nbr, rng)
        if nn is None: continue
        cn = cost(nn)
        if cn <= c or rng.random() < math.exp(-(cn - c) / T):
            nbr, c = nn, cn; acc += 1
            if c < bestc:
                bestc = c
                np.save(out + '_best.npy', nbr)
                print(f"step {step} t={time.time()-t0:.0f}s cost={c} T={T:.2f}", flush=True)
                if c == 0:
                    print("COST 0: verifying with independent BFS", flush=True)
                    ecc = check_full(nbr)
                    print(f"full BFS max eccentricity = {ecc}", flush=True)
                    break
        if step % 200 == 0:
            print(f"step {step} t={time.time()-t0:.0f}s cur={c} best={bestc} acc={acc} T={T:.2f}", flush=True)
    print(f"end steps={step} best={bestc}", flush=True)
