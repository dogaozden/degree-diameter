import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: annealing search for bi-Cayley lifts over Z_m x| Z_k2.
#
# Vertices: A_{i,g} = i*G + g (i < K), B_{j,h} = (K+j)*G + h, G = m*k2.
# Layer l joins A_i to B_{p} with p = layers[l][i] through voltage s:
# A_{i,g} ~ B_{p, g*s}. Each layer is a permutation of the K blocks, so
# every vertex has degree DEG exactly. The graph is bipartite by construction.
#
# Diameter is checked with bitmasks over the 2K block representatives.
# Left multiplication is an automorphism, so this covers all pairs.
# Groups, base sizes and voltages are sampled inside C; the search keeps
# the largest order that reaches zero cost.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDEG 32
#define MAXK 8
#define MAXN 60000
#define PEN 1000

static int DEG, DIAM, KB, K2, M, RR, G, N;
static uint32_t FULLM;
static int powr[64];
static int layers[MAXDEG][MAXK];
static int ilayer[MAXDEG][MAXK];
static int SV[MAXDEG][MAXK];
static int nbr[MAXDEG][MAXN];
static uint32_t bufA[MAXN], bufB[MAXN], tmpR[MAXN];
static uint32_t *cur, *nw;
static unsigned char PC[65536];
static uint64_t rs = 88172645463325252ULL;

static int have_best = 0;
static int bestKB, bestK2, bestM, bestR, bestN;
static int bestLayers[MAXDEG][MAXK];
static int bestSV[MAXDEG][MAXK];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_sec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static long long powmod(long long b, int e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static void setup_group(int kb, int k2, int m, int r) {
    KB = kb;
    K2 = k2;
    M = m;
    RR = r;
    G = m * k2;
    N = 2 * kb * G;
    FULLM = (1u << (2 * kb)) - 1u;
    powr[0] = 1 % m;
    for (int t = 1; t < k2; t++) powr[t] = (int)(((long long)powr[t - 1] * r) % m);
}

/* (a,b)(c,e) = (a + r^b c, b + e) with a in Z_M, b in Z_K2; element = a*K2 + b. */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    int t = (int)(((long long)a + (long long)powr[b] * c) % M);
    return t * K2 + (b + e) % K2;
}

/* Inverse of (a,b) is (-r^(-b) a, -b). */
static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long long t = ((long long)powr[nb] * a) % M;
    int na = (int)((M - t) % M);
    return na * K2 + nb;
}

static void build_nbr(void) {
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < KB; i++) {
            int j = layers[l][i], s = SV[l][i];
            for (int g = 0; g < G; g++)
                nbr[l][i * G + g] = (KB + j) * G + gmul(g, s);
        }
        for (int j = 0; j < KB; j++) {
            int i = ilayer[l][j];
            int si = ginv(SV[l][i]);
            for (int h = 0; h < G; h++)
                nbr[l][(KB + j) * G + h] = i * G + gmul(h, si);
        }
    }
}

/* Repeated (base vertex, voltage) pairs for the same A-block create parallel edges. */
static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < KB; i++)
        for (int l1 = 0; l1 < DEG; l1++)
            for (int l2 = l1 + 1; l2 < DEG; l2++)
                if (layers[l1][i] == layers[l2][i] && SV[l1][i] == SV[l2][i]) c++;
    return c;
}

/* Fills res with per-vertex reach masks; returns the number of unreached (block, vertex) pairs. */
static int eval_reach(uint32_t *res) {
    int NB = 2 * KB;
    uint32_t full = (1u << NB) - 1u;
    uint32_t *a = res, *b = tmpR;
    for (int v = 0; v < N; v++) a[v] = 0;
    for (int blk = 0; blk < NB; blk++) a[blk * G] |= (1u << blk);
    for (int step = 0; step < DIAM; step++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = a[v];
            for (int l = 0; l < DEG; l++) x |= a[nbr[l][v]];
            b[v] = x;
            if (x != a[v]) changed = 1;
        }
        uint32_t *t = a;
        a = b;
        b = t;
        if (!changed) break;
    }
    if (a != res) memcpy(res, a, sizeof(uint32_t) * (size_t)N);
    int unr = 0;
    for (int v = 0; v < N; v++) unr += NB - PC[res[v] & full];
    return unr;
}

static void layer_swap(int l, int i1, int i2) {
    int t = layers[l][i1];
    layers[l][i1] = layers[l][i2];
    layers[l][i2] = t;
    ilayer[l][layers[l][i1]] = i1;
    ilayer[l][layers[l][i2]] = i2;
}

static int anneal(long long iters, long long patience, double deadline) {
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < KB; i++) layers[l][i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = layers[l][i];
            layers[l][i] = layers[l][j];
            layers[l][j] = t;
        }
        for (int i = 0; i < KB; i++) ilayer[l][layers[l][i]] = i;
        for (int i = 0; i < KB; i++) SV[l][i] = rndint(G);
    }
    build_nbr();
    int dup = dupcount();
    int unr = eval_reach(cur);
    long long cost = (long long)unr + (long long)PEN * dup;
    double c0 = cost > 1 ? (double)cost : 1.0;
    long long best = cost, last = 0;

    for (long long t = 0; t < iters; t++) {
        if (cost == 0) break;
        if ((t & 63) == 0 && now_sec() > deadline) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;
        double x = rnd01();

        if (KB >= 2 && x < 0.25) {
            int l = rndint(DEG);
            int i1 = rndint(KB);
            int i2 = rndint(KB - 1);
            if (i2 >= i1) i2++;
            layer_swap(l, i1, i2);
            build_nbr();
            dup = dupcount();
            unr = eval_reach(nw);
            long long c2 = (long long)unr + (long long)PEN * dup;
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                uint32_t *tp = cur;
                cur = nw;
                nw = tp;
                if (cost < best) {
                    best = cost;
                    last = t;
                }
            } else {
                layer_swap(l, i1, i2);
            }
            continue;
        }

        int l = rndint(DEG);
        int i = rndint(KB);
        if (rnd01() < 0.4) {
            for (int tr = 0; tr < 60; tr++) {
                int v = rndint(N);
                if (cur[v] != FULLM) {
                    int blk = v / G;
                    if (blk < KB) i = blk;
                    else i = ilayer[l][blk - KB];
                    break;
                }
            }
        }
        int old = SV[l][i];
        int nv = rndint(G);
        if (nv == old) continue;
        SV[l][i] = nv;
        build_nbr();
        dup = dupcount();
        unr = eval_reach(nw);
        long long c2 = (long long)unr + (long long)PEN * dup;
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            uint32_t *tp = cur;
            cur = nw;
            nw = tp;
            if (cost < best) {
                best = cost;
                last = t;
            }
        } else {
            SV[l][i] = old;
        }
    }
    return cost == 0;
}

static void save_best(void) {
    have_best = 1;
    bestKB = KB;
    bestK2 = K2;
    bestM = M;
    bestR = RR;
    bestN = N;
    memcpy(bestLayers, layers, sizeof(layers));
    memcpy(bestSV, SV, sizeof(SV));
}

static void output_best(void) {
    setup_group(bestKB, bestK2, bestM, bestR);
    memcpy(layers, bestLayers, sizeof(layers));
    memcpy(SV, bestSV, sizeof(SV));
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < KB; i++) ilayer[l][layers[l][i]] = i;
    build_nbr();
    long long m = (long long)KB * G * DEG;
    printf("%d %lld\n", N, m);
    for (int v = 0; v < KB * G; v++)
        for (int l = 0; l < DEG; l++)
            printf("%d %d\n", v, nbr[l][v]);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int floor_n = atoi(argv[5]);
    int kmax = (argc > 6) ? atoi(argv[6]) : 6;
    char sink[256];
    while (fread(sink, 1, sizeof sink, stdin) > 0) {
    }
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    if (kmax > MAXK) kmax = MAXK;
    if (kmax < 1) kmax = 1;

    PC[0] = 0;
    for (int x = 1; x < 65536; x++) PC[x] = (unsigned char)(PC[x >> 1] + (x & 1));

    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;

    cur = bufA;
    nw = bufB;
    double deadline = now_sec() + tl;
    int best_n = floor_n;

    static const int KS[] = {1, 2, 2, 3, 3, 4, 4, 5, 6, 6, 7, 8};
    static const int K2S[] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12};
    const int nks = (int)(sizeof KS / sizeof KS[0]);
    const int nk2 = (int)(sizeof K2S / sizeof K2S[0]);

    while (now_sec() < deadline) {
        int kb;
        do {
            kb = KS[rndint(nks)];
        } while (kb > kmax);
        int k2 = K2S[rndint(nk2)];

        long long gmin = (long long)best_n / (2LL * kb) + 1;
        long long mm = (gmin + k2 - 1) / k2;
        long long jit = 1 + mm / 40;
        mm += (long long)rndint((int)jit);
        if (mm < 2) mm = 2;
        long long Nn = 2LL * kb * mm * k2;
        if (Nn > MAXN) continue;

        int m = (int)mm;
        int r = 1 % m;
        if (k2 >= 2 && m >= 3) {
            int found = 0;
            for (int tr = 0; tr < 100 && !found; tr++) {
                int c = 2 + rndint(m - 2);
                if (gcd_i(c, m) == 1 && powmod((long long)c, k2, m) == 1 % m) {
                    r = c;
                    found = 1;
                }
            }
            if (!found && k2 == 2) r = m - 1;
        }

        setup_group(kb, k2, m, r);
        if (N > MAXN) continue;
        int ok = anneal(20000, 2500, deadline);
        if (ok && N > best_n) {
            best_n = N;
            save_best();
        }
    }

    if (have_best) output_best();
    else printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions (unchanged from the parent).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


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
# Python search (parent): bi-Cayley lifts with simulated annealing.
# Kept as a second search stage, seeded by the C engine's best graph.
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


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
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
    Ts = np.ascontiguousarray(M.T)
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
    """Simulated annealing with stagnation restarts. Returns (n, edges) or None."""
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


def _seed_arg(seed):
    """Non-negative integer seed for the C engine."""
    return int(seed) & 0xFFFFFFFFFFFF


def build(d, D, seed, time_limit):
    start = time.monotonic()
    usable_end = start + max(1.0, min(0.85 * time_limit, time_limit - 7.0))
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

    if D == 2:
        return best

    # Exact constructions: return immediately for calibration-style cases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < usable_end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Stage 1: C annealing engine over semidirect lifts with larger base sizes.
    c_budget = 0.55 * (usable_end - time.monotonic())
    if c_budget >= 2.0 and d <= 32:
        try:
            out = lib.run_c(C_SOURCE, [d, D, _seed_arg(seed), round(c_budget, 2), best_n, 6],
                            stdin_graph=None, timeout=c_budget + 10.0)
            n_c, e_c = lib.parse_graph_text(out)
            consider(n_c, e_c)
        except Exception:
            pass

    # Stage 2: Python bi-Cayley annealing for the remaining budget.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < usable_end:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, usable_end, 4000, 1200)
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
