# Algebraically defined cubic bipartite graphs B(f_2..f_k), coordinate i of points/lines lives in Z_{ms[i-1]}.
# Point p=(p1..pk), line l=(l1..lk); p ~ l iff  l_i + p_i = f_i(p1,l1,...,p_{i-1},l_{i-1}) (mod ms[i-1]), i=2..k.
# p1, l1 in {0,1,2} (ms[0]=3) so every point (fix l1) and every line (fix p1) has exactly 3 neighbours.
import ctypes, os, random, itertools, sys
HERE = os.path.dirname(os.path.abspath(__file__))
_lib = ctypes.CDLL(os.path.join(HERE, 'libscore.so'))
_lib.score.restype = ctypes.c_int
_lib.score.argtypes = [ctypes.c_int, ctypes.POINTER(ctypes.c_int), ctypes.POINTER(ctypes.c_int)]

def build(ms, fs):
    """ms: moduli list (len k, ms[0]=3). fs: list (len k-1) of dicts {monomial: coef}; monomial = tuple of
    variables ('p',j) / ('l',j), 1-based j, all with j < i; () is the constant. Returns (n, adj list of 3n ints)."""
    k = len(ms)
    N = 1
    for m in ms: N *= m
    def idx(t):
        r = 0
        for j in range(k): r = r * ms[j] + t[j]
        return r
    adj = [0] * (3 * 2 * N)  # rows: points then lines; each 3 entries
    deg = [0] * (2 * N)
    for pt in itertools.product(*[range(m) for m in ms]):
        pi = idx(pt)
        if pt[0] >= 3: continue
        # only p1 in 0..2 is valid: ms[0]=3 so product covers it
        for a in range(3):
            L = [a]
            for i in range(2, k + 1):
                env = {}
                for j in range(1, i):
                    env[('p', j)] = pt[j - 1]
                    env[('l', j)] = L[j - 1]
                m = ms[i - 1]
                val = 0
                for mono, c in fs[i - 2].items():
                    t = c
                    for v in mono: t *= env[v]
                    val += t
                L.append((val - pt[i - 1]) % m)
            li = N + idx(L)
            adj[3 * pi + deg[pi]] = li; deg[pi] += 1
            adj[3 * li + deg[li]] = pi; deg[li] += 1
    if any(d != 3 for d in deg):
        return None
    return 2 * N, adj

def score(n, adj):
    arr = (ctypes.c_int * len(adj))(*adj)
    d = ctypes.c_int(0)
    bad = _lib.score(n, arr, ctypes.byref(d))
    return bad, d.value

def write_edges(n, adj, path):
    with open(path, 'w') as f:
        E = set()
        for u in range(n):
            for e in range(3):
                v = adj[3 * u + e]
                if u < v: E.add((u, v))
        f.write(f"{n}\n")
        for u, v in sorted(E): f.write(f"{u} {v}\n")
        return len(E)
