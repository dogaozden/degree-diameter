"""Card c6: anneal the other matchings (and the freed arcs' matchings, R fixed) at q=7, 7 levels, all H, rotational
tournament j -> j+1,j+2,j+3, so that the whole graph (no hubs) has diameter 5.
Objective: number of unordered pairs at distance > 5 in the whole graph (exact, bit-parallel BFS in bad7.so).
Moves: 'rand' = swap two images in one matching; 'targ' = for a random bad pair (x,v), choose p in ball_a(x), q in
ball_b(v), a+b=4, p a point and q a line with lev(q)-lev(p) mod 7 in {1,2,3}, and set M_t(p)=q by swapping with the
preimage of q (t = arc lev(p)->lev(q)); 'mix' = 50/50.
Usage: sa7.py mode arcs(one of: 1,2,4) s steps seed T0 [tag]"""
import sys, time, math, pickle, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r2/c6')
from common7 import *
import gqlib

mode, narcs, s, steps, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
T0 = float(sys.argv[6]) if len(sys.argv) > 6 else 1.0
tag = sys.argv[7] if len(sys.argv) > 7 else ''
G = gqlib.Q4(7)
net = Net(G)
NP, PER = G.np, G.np + G.nl
rng = np.random.default_rng(seed)
FREE = {1: [(0, 1)], 2: [(0, 1), (2, 3)], 4: [(0, 1), (2, 3), (4, 5), (6, 0)]}[narcs]
M = {a: rng.permutation(NP) for a in net.arcs}
R = {a: set(rng.choice(NP, s, replace=False).tolist()) for a in FREE}
inv = {a: np.argsort(M[a]) for a in net.arcs}   # inv[a][line] = point
tag = tag or 'c6_%s_a%d_s%d_seed%d' % (mode, narcs, s, seed)

def build_adj(eu, ev, n):
    src = np.concatenate([eu, ev]).astype(np.int64); dst = np.concatenate([ev, eu]).astype(np.int64)
    order = np.argsort(src, kind='stable'); src_s = src[order]; dst_s = dst[order]
    cnt = np.bincount(src_s, minlength=n); starts = np.concatenate([[0], np.cumsum(cnt)[:-1]])
    pos = np.arange(len(src_s)) - starts[src_s]
    adj = -np.ones((n, cnt.max()), np.int64); adj[src_s, pos] = dst_s
    return adj

def shells(adj, n, src, depth=4):
    vis = np.zeros(n, bool); vis[src] = True
    out = [np.array([src])]; f = np.array([src])
    for d in range(depth):
        nb = adj[f].ravel(); nb = nb[nb >= 0]
        new = np.unique(nb[~vis[nb]]); vis[new] = True
        out.append(new); f = new
    return out

def evaluate(Mc):
    eu, ev = net.edges(Mc, R)
    tot, pairs = net.bad_pairs(Mc, R, maxpairs=20000)
    return tot, pairs, eu, ev

def is_point(v): return (v % PER) < NP
def lev(v): return v // PER

def targeted(Mc, pairs, eu, ev):
    """propose a swapped Mc' from a random bad pair. A new edge (P,Lr) (P a point, Lr a line, levels i -> i+k, k in 1..3)
    closes a path x..P-Lr..v of length a+1+b. Need length <= 4 if x,v have the same type (bipartite parity), else <= 5."""
    n = net.n
    adj = build_adj(eu, ev, n)
    for _ in range(20):
        x, v = pairs[rng.integers(len(pairs))]
        if rng.random() < 0.5: x, v = v, x
        x = int(x); v = int(v)
        tot_len = 4 if is_point(x) == is_point(v) else 5
        Sx = shells(adj, n, x); Sv = shells(adj, n, v)
        opts = [(a, b) for a in range(tot_len) for b in range(tot_len) if a + b <= tot_len - 1]
        for _t in range(60):
            a, b = opts[rng.integers(len(opts))]
            if len(Sx[a]) == 0 or len(Sv[b]) == 0: continue
            p = int(Sx[a][rng.integers(len(Sx[a]))]); q = int(Sv[b][rng.integers(len(Sv[b]))])
            if is_point(p) == is_point(q): continue
            P, Lr = (p, q) if is_point(p) else (q, p)
            if (lev(Lr) - lev(P)) % L not in (1, 2, 3): continue
            t = (lev(P), lev(Lr)); pa = P % PER; lb = Lr % PER - NP
            if Mc[t][pa] == lb: continue
            Mn = {k: Mc[k] for k in Mc}
            Mt = Mn[t].copy(); pre = int(np.nonzero(Mt == lb)[0][0])
            old = Mt[pa]; Mt[pa] = lb; Mt[pre] = old; Mn[t] = Mt
            return Mn
    return None

cur_M = M; cur_bad, cur_pairs, eu, ev = evaluate(cur_M)
best = cur_bad; best_M = {k: v.copy() for k, v in cur_M.items()}
print('start bad(unordered, whole)', cur_bad, flush=True)
t0 = time.time(); nacc = 0
for it in range(steps):
    T = T0 * (1 - it / steps) + 0.02
    use_t = (mode == 'targ') or (mode == 'mix' and rng.random() < 0.5)
    new_M = None
    if use_t and len(cur_pairs):
        new_M = targeted(cur_M, cur_pairs, eu, ev)
    if new_M is None:
        t = net.arcs[rng.integers(len(net.arcs))]
        a, b = rng.choice(NP, 2, replace=False)
        new_M = {k: cur_M[k] for k in cur_M}; Mt = cur_M[t].copy(); Mt[a], Mt[b] = Mt[b], Mt[a]; new_M[t] = Mt
    nb, npairs, neu, nev = evaluate(new_M)
    d = nb - cur_bad
    if d <= 0 or rng.random() < math.exp(-d / T):
        cur_M, cur_bad, cur_pairs, eu, ev = new_M, nb, npairs, neu, nev; nacc += 1
        if cur_bad < best:
            best = cur_bad; best_M = {k: v.copy() for k, v in cur_M.items()}
            if best == 0: break
    if it % 200 == 0:
        print('it', it, 'cur', cur_bad, 'best', best, 'acc', nacc, 'T %.2f' % T, 'el %.0f' % (time.time() - t0), flush=True)
print('FINAL %s best=%d steps=%d el=%.0f' % (tag, best, it + 1, time.time() - t0), flush=True)
pickle.dump({'arcs': net.arcs, 's': s, 'narcs': narcs, 'FREE': FREE, 'best': best, 'M': best_M, 'R': R, 'seed': seed},
            open('/home/user/degree-diameter/research/squads/gqd5-r2/c6/state_%s.pkl' % tag, 'wb'))
if best == 0:
    eu, ev = net.edges(best_M, R)
    write_edges('/home/user/degree-diameter/research/squads/gqd5-r2/c6/%s.edges' % tag, net.n, eu, ev)
    print('edges written', tag, flush=True)
