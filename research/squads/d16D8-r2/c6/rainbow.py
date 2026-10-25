# c6 rainbow hypothesis: proper (q+3)-edge-colouring of I + M1 + M2 (I = incidence graph of W(q)).
# colours 0..q: a 1-factorization of I; colour q+1 = M1, colour q+2 = M2 (random perfect matchings).
# voltage of an edge of colour c, oriented point -> line: CRT element v in Z_{5k} with v = level(c) mod 5 and
# v = f(c) mod k, level = 0 (flags), 1 (M1), 2 (M2); f maps the q+3 colours 2-to-1 onto Z_k \ {0}, k = (q+5)/2.
import sys, os, json, random, subprocess
from collections import deque
sys.setrecursionlimit(100000)
sys.path.insert(0, '/home/user/degree-diameter/research/d16D8')
import gq

BASELIFT = '/home/user/degree-diameter/research/d16D8/baselift'
HERE = os.path.dirname(os.path.abspath(__file__))

def hopcroft_karp(adj, nL, nR):
    INF = 1 << 30
    matchL = [-1] * nL; matchR = [-1] * nR
    dist = [0] * nL
    def bfs():
        dq = deque(); found = False
        for u in range(nL):
            if matchL[u] == -1:
                dist[u] = 0; dq.append(u)
            else:
                dist[u] = INF
        while dq:
            u = dq.popleft()
            for v in adj[u]:
                w = matchR[v]
                if w == -1:
                    found = True
                elif dist[w] == INF:
                    dist[w] = dist[u] + 1; dq.append(w)
        return found
    def dfs(u):
        for v in adj[u]:
            w = matchR[v]
            if w == -1 or (dist[w] == dist[u] + 1 and dfs(w)):
                matchL[u] = v; matchR[v] = u
                return True
        dist[u] = INF
        return False
    res = 0
    while bfs():
        for u in range(nL):
            if matchL[u] == -1 and dfs(u):
                res += 1
    return matchL, res

def factorize(q, seed):
    """1-factorization of I (points 0..N-1 -> lines 0..N-1): returns list of q+1 matchings, each a list pt -> line index."""
    G = gq.load(q); N = G['N']; rnd = random.Random(seed)
    rem = [list(G['plines'][p]) for p in range(N)]
    for p in range(N):
        rnd.shuffle(rem[p])
    mats = []
    for c in range(q + 1):
        M, r = hopcroft_karp(rem, N, N)
        assert r == N, ('no perfect matching', c, r)
        mats.append(M)
        for p in range(N):
            rem[p].remove(M[p])
    return mats

def crt(a5, bk, k):
    for v in range(5 * k):
        if v % 5 == a5 and v % k == bk % k:
            return v
    raise ValueError

def level_of(q, c):
    return 0 if c <= q else (1 if c == q + 1 else 2)

def build(q, seed, f=None, mats=None, Mrand=None, k=None):
    """returns (V, m, edges, info). f: list of length q+3 (colour -> nonzero element of Z_k)."""
    G = gq.load(q); N = G['N']; rnd = random.Random(seed * 7919 + 13)
    if k is None:
        k = (q + 5) // 2
    m = 5 * k
    if mats is None:
        mats = factorize(q, seed)
    if Mrand is None:
        Mrand = []
        for t in range(2):
            perm = list(range(N)); rnd.shuffle(perm); Mrand.append(perm)
    colour_match = [mats[c] for c in range(q + 1)] + Mrand
    if f is None:
        vals = []
        for z in range(1, k):
            vals += [z, z]
        rnd.shuffle(vals)
        f = vals
    volt = [crt(level_of(q, c), f[c], k) for c in range(q + 3)]
    edges = []
    for c in range(q + 3):
        M = colour_match[c]
        for p in range(N):
            edges.append((p, N + M[p], volt[c], 1 if c <= q else 100 + (c - q - 1)))
    return 2 * N, m, edges, dict(f=f, volt=volt, k=k, m=m)

def write_design(fn, q, seed, f=None, mats=None, Mrand=None, k=None):
    V, m, edges, info = build(q, seed, f=f, mats=mats, Mrand=Mrand, k=k)
    gq.write_base(fn, V, m, edges)
    return info

def evaluate(fn, D=6, nsrc=None, extra_env=None):
    env = dict(os.environ); env['THREADS'] = '1'
    if extra_env: env.update(extra_env)
    cmd = [BASELIFT, 'eval', fn, str(D)] + ([str(nsrc)] if nsrc else [])
    out = subprocess.run(cmd, capture_output=True, text=True, env=env).stdout.strip()
    unc = int(out.split('uncovered=')[1].split()[0])
    return unc, out, ('VALID(all sources)' in out)

if __name__ == '__main__':
    import time
    q = int(sys.argv[1]); seed = int(sys.argv[2]); fn = sys.argv[3]
    t0 = time.time()
    info = write_design(fn, q, seed)
    print('built', fn, 'k=', info['k'], 'm=', info['m'], 'f=', info['f'], 'volt=', info['volt'], 'time=%.1f' % (time.time() - t0))
    unc, out, valid = evaluate(fn, 6)
    print(out, 'VALID' if valid else 'not valid', 'time=%.1f' % (time.time() - t0))
