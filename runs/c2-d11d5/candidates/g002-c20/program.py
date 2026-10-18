import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts on Z_m x| Z_k2.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h, G = m*k2.
# Layer l pairs A_i with B_{lay[l][i]} via voltage s: A_{i,g} ~ B_{g*s}.
# Every layer is a permutation, so the lift is d-regular. Left multiplication
# is an automorphism, so the diameter test only needs the 2k block starts.
# Usage: prog d D seed time_limit k m k2 r iters patience
# Prints "N E" and the edges on success, or "0 0".
# ----------------------------------------------------------------------------

_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 6
#define MAXG 400000LL

static int d, D, k, m, k2, r;
static long long G, N;
static long long *pw;
static long long *invel;
static int *lay;
static long long *S;
static int32_t *nbr;
static unsigned char pc[4096];
static uint64_t rs = 88172645463325252ULL;
static uint64_t *bufA, *bufB, *bufC;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static long long rndi(long long n) {
    return (long long)(rnd() % (uint64_t)n);
}

static double rndu(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static double cpu_secs(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC;
}

static long long gmul(long long x, long long y) {
    long long a = x / k2, b = x % k2;
    long long c = y / k2, e = y % k2;
    return ((a + pw[b] * c) % m) * k2 + (b + e) % k2;
}

static void set_dart(int l, int i, int j, long long s) {
    long long is = invel[s];
    int32_t *nb = nbr + (long long)l * N;
    long long Bbase = (long long)(k + j) * G;
    long long Abase = (long long)i * G;
    for (long long g = 0; g < G; g++) {
        nb[Abase + g] = (int32_t)(Bbase + gmul(g, s));
        nb[Bbase + g] = (int32_t)(Abase + gmul(g, is));
    }
}

/* Writes block-start bits into out, then propagates D rounds.
   Returns whichever of out/tmp holds the final result. */
static uint64_t *compute_reach(uint64_t *out, uint64_t *tmp) {
    long long K2 = 2LL * k;
    for (long long v = 0; v < N; v++) out[v] = 0;
    for (long long b = 0; b < K2; b++) out[b * G] |= (1ULL << b);
    uint64_t *cur = out, *nxt = tmp;
    for (int it = 0; it < D; it++) {
        int changed = 0;
        for (long long v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[(long long)l * N + v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    return cur;
}

static long long unreached(const uint64_t *R) {
    long long s = 0;
    for (long long v = 0; v < N; v++) s += pc[R[v] & 4095];
    return 2LL * k * N - s;
}

static long long dupcount(void) {
    long long c = 0;
    int tot = d * k;
    for (int p = 0; p < tot; p++) {
        int ip = p % k;
        for (int q = 0; q < p; q++) {
            if (q % k == ip && lay[p] == lay[q] && S[p] == S[q]) {
                c++;
                break;
            }
        }
    }
    return c;
}

int main(int argc, char **argv) {
    if (argc < 11) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    k = atoi(argv[5]);
    m = atoi(argv[6]);
    k2 = atoi(argv[7]);
    r = atoi(argv[8]);
    long long iters = atoll(argv[9]);
    long long patience = atoll(argv[10]);
    if (d < 1 || D < 1 || k < 1 || k > MAXK || m < 2 || k2 < 1) {
        printf("0 0\n");
        return 0;
    }
    G = (long long)m * k2;
    if (G > MAXG) {
        printf("0 0\n");
        return 0;
    }
    N = 2LL * k * G;
    r %= m;
    if (r < 0) r += m;

    pw = malloc(sizeof(long long) * k2);
    invel = malloc(sizeof(long long) * G);
    lay = malloc(sizeof(int) * d * k);
    S = malloc(sizeof(long long) * d * k);
    nbr = malloc(sizeof(int32_t) * (size_t)d * (size_t)N);
    bufA = malloc(sizeof(uint64_t) * (size_t)N);
    bufB = malloc(sizeof(uint64_t) * (size_t)N);
    bufC = malloc(sizeof(uint64_t) * (size_t)N);
    if (!pw || !invel || !lay || !S || !nbr || !bufA || !bufB || !bufC) {
        printf("0 0\n");
        return 0;
    }

    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = pw[b - 1] * r % m;
    if ((pw[k2 - 1] * r) % m != 1 % m) {
        printf("0 0\n");
        return 0;
    }
    for (long long x = 0; x < G; x++) {
        long long a = x / k2, b = x % k2;
        long long nb = (k2 - b) % k2;
        long long na = (m - (pw[nb] * a) % m) % m;
        invel[x] = na * k2 + nb;
    }
    for (int u = 0; u < 256; u++) {
        int c = 0;
        for (int v = u; v; v >>= 1) c += v & 1;
        pc[u] = (unsigned char)c;
    }
    for (int u = 256; u < 4096; u++) pc[u] = (unsigned char)(pc[u >> 8] + pc[u & 255]);

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 10; w++) rnd();

    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = (int)rndi(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < k; i++) lay[l * k + i] = perm[i];
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) S[l * k + i] = rndi(G);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) set_dart(l, i, lay[l * k + i], S[l * k + i]);

    const long long PEN = 1000;
    uint64_t full = (1ULL << (2 * k)) - 1;

    uint64_t *R = compute_reach(bufA, bufB);
    uint64_t *F1 = (R == bufA) ? bufB : bufA;
    uint64_t *F2 = bufC;

    long long cost = unreached(R) + PEN * dupcount();
    double c0 = cost > 1 ? (double)cost : 1.0;
    long long best_cost = cost, last = 0;

    for (long long t = 0; t < iters; t++) {
        if (cost == 0) break;
        if (cpu_secs() > tl) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;
        double x = rndu();

        if (k >= 2 && x < 0.25) {
            int l = (int)rndi(d);
            int i1 = (int)rndi(k);
            int i2 = (int)rndi(k - 1);
            if (i2 >= i1) i2++;
            int p1 = l * k + i1, p2 = l * k + i2;
            int tmp = lay[p1];
            lay[p1] = lay[p2];
            lay[p2] = tmp;
            set_dart(l, i1, lay[p1], S[p1]);
            set_dart(l, i2, lay[p2], S[p2]);
            uint64_t *res = compute_reach(F1, F2);
            uint64_t *oth = (res == F1) ? F2 : F1;
            long long c2 = unreached(res) + PEN * dupcount();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                uint64_t *old = R;
                R = res;
                F1 = old;
                F2 = oth;
                cost = c2;
                if (cost < best_cost) {
                    best_cost = cost;
                    last = t;
                }
            } else {
                tmp = lay[p1];
                lay[p1] = lay[p2];
                lay[p2] = tmp;
                set_dart(l, i1, lay[p1], S[p1]);
                set_dart(l, i2, lay[p2], S[p2]);
                F1 = res;
                F2 = oth;
            }
            continue;
        }

        int l = -1, i = -1;
        int found = 0;
        if (rndu() < 0.4) {
            long long cnt = 0, pick = -1;
            for (long long v = 0; v < N; v++) {
                if (R[v] != full) {
                    cnt++;
                    if (rnd() % (uint64_t)cnt == 0) pick = v;
                }
            }
            if (pick >= 0) {
                long long block = pick / G;
                l = (int)rndi(d);
                if (block < k) {
                    i = (int)block;
                } else {
                    i = -1;
                    for (int q = 0; q < k; q++) {
                        if (lay[l * k + q] == block - k) {
                            i = q;
                            break;
                        }
                    }
                    if (i < 0) i = (int)rndi(k);
                }
                found = 1;
            }
        }
        if (!found) {
            l = (int)rndi(d);
            i = (int)rndi(k);
        }
        int p = l * k + i;
        long long old = S[p];
        long long nw = rndi(G);
        if (nw == old) continue;
        S[p] = nw;
        set_dart(l, i, lay[p], nw);
        uint64_t *res = compute_reach(F1, F2);
        uint64_t *oth = (res == F1) ? F2 : F1;
        long long c2 = unreached(res) + PEN * dupcount();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
            uint64_t *oldR = R;
            R = res;
            F1 = oldR;
            F2 = oth;
            cost = c2;
            if (cost < best_cost) {
                best_cost = cost;
                last = t;
            }
        } else {
            S[p] = old;
            set_dart(l, i, lay[p], old);
            F1 = res;
            F2 = oth;
        }
    }

    if (cost == 0) {
        long long E = (long long)k * G * d;
        printf("%lld %lld\n", N, E);
        for (long long u = 0; u < (long long)k * G; u++)
            for (int l = 0; l < d; l++)
                printf("%lld %d\n", u, (int)nbr[(long long)l * N + u]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Slack extension: add new vertices using spare degree, accepting only
# graphs that pass lib.is_valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Group sampling and a Python fallback search (used only if the C engine fails).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4, 5, 6)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))  # ceil, so the order is at least target
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1  # dihedral-type: (a,b)(c,e) = (a + (-1)^b c, b+e)
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                r = None
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b is set when representative block b is within distance D."""
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    """Number of unreached (representative, vertex) pairs."""
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Python simulated annealing (fallback). Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))
    best_cost = cost
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last_improve > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last_improve = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            if cost < best_cost:
                best_cost, last_improve = cost, t
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


def _c_trial(d, D, seed, tl, k, m, k2, r, iters, patience):
    """Run one C annealing trial. Returns (n, edges) or None."""
    text = lib.run_c(_C_SOURCE, [d, D, seed, f"{tl:.3f}", k, m, k2, r, iters, patience],
                     timeout=tl + 10.0)
    head = text.split()[:2]
    if len(head) < 2 or head == ["0", "0"]:
        return None
    return lib.parse_graph_text(text)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    final_deadline = start + max(1.0, time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except (ValueError, RuntimeError):
                pass

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: bandit over base sizes k, C engine first.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    use_c = True

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G = m * k2
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        res = None
        if use_c:
            remaining = deadline - time.monotonic()
            tl = min(4.0, max(0.2, remaining))
            try:
                res = _c_trial(d, D, rng.randrange(1 << 30), tl, k, m, k2, r, 4000, 1200)
            except (RuntimeError, ValueError):
                use_c = False
                res = None
        if not use_c:
            _, Ts, Invs = _semidirect_tables(m, k2, r)
            res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
