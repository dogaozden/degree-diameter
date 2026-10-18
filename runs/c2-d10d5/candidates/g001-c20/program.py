import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: random-start degree-preserving search on bipartite graphs.
#
# State: bipartite graph (side 0 / side 1) with max degree d. Moves are
# double-edge switches (degree-preserving) and pair insertions (two new
# vertices, one per side, that take over the endpoints of k removed edges,
# so degrees are kept). Cost = number of (source, vertex) pairs at distance
# > D, computed with bitsets over a sample of sources. Sampled zero is
# confirmed by an exact check over all vertices before a snapshot is kept.
# The best exactly-valid graph is printed at the end.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define KS 512
#define STEPS 400
#define MAXN_CAP 20000

typedef uint64_t u64;

static int d_, D_, maxn;
static int n;
static int *side, *deg, *nb;
static u64 *bufA, *bufB;
static int *curbad, *candbad, *tmpbad, *ident, *src, *badlist;
static int *snap_deg, *snap_nb, *usedv;
static int ksrc, nbad, snap_n, have_snap, stamp;
static u64 rs;
static double deadline;

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static u64 rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int m) { return (int)(rnd64() % (u64)m); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int has_edge(int a, int b) {
    const int *p = nb + (size_t)a * d_;
    for (int i = 0; i < deg[a]; i++)
        if (p[i] == b) return 1;
    return 0;
}

static void del_one(int a, int b) {
    int *p = nb + (size_t)a * d_;
    for (int i = 0; i < deg[a]; i++) {
        if (p[i] == b) {
            p[i] = p[--deg[a]];
            return;
        }
    }
}

static void add_edge(int a, int b) {
    nb[(size_t)a * d_ + deg[a]++] = b;
    nb[(size_t)b * d_ + deg[b]++] = a;
}

static void remove_edge(int a, int b) {
    del_one(a, b);
    del_one(b, a);
}

/* badv[v] = number of sources s (among the k given) with dist(v, s) > D_.
   Returns the sum of badv. */
static long eval_src(const int *S, int k, int *badv) {
    int W = (k + 63) >> 6;
    u64 *R = bufA, *T = bufB;
    memset(R, 0, sizeof(u64) * (size_t)n * W);
    for (int j = 0; j < k; j++)
        R[(size_t)S[j] * W + (j >> 6)] |= 1ULL << (j & 63);
    for (int r = 0; r < D_; r++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            u64 *o = T + (size_t)v * W;
            const u64 *s = R + (size_t)v * W;
            memcpy(o, s, sizeof(u64) * (size_t)W);
            const int *p = nb + (size_t)v * d_;
            for (int i = 0; i < deg[v]; i++) {
                const u64 *t = R + (size_t)p[i] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
            if (!changed) {
                for (int w = 0; w < W; w++) {
                    if (o[w] != s[w]) {
                        changed = 1;
                        break;
                    }
                }
            }
        }
        u64 *tmp = R;
        R = T;
        T = tmp;
        if (!changed) break;
    }
    long tot = 0;
    for (int v = 0; v < n; v++) {
        const u64 *s = R + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        badv[v] = k - c;
        tot += k - c;
    }
    return tot;
}

static int rand_edge(int *a, int *b) {
    if (n < 2) return 0;
    for (int tr = 0; tr < 200; tr++) {
        int x = rndint(n);
        if (deg[x] == 0) continue;
        int y = nb[(size_t)x * d_ + rndint(deg[x])];
        if (side[x] == 0) {
            *a = x;
            *b = y;
        } else {
            *a = y;
            *b = x;
        }
        return 1;
    }
    return 0;
}

static int try_switch(int *oa1, int *ob1, int *oa2, int *ob2, int focus) {
    int a1 = 0, b1 = 0, a2 = 0, b2 = 0;
    if (focus >= 0) {
        if (deg[focus] == 0) return 0;
        int y = nb[(size_t)focus * d_ + rndint(deg[focus])];
        if (side[focus] == 0) {
            a1 = focus;
            b1 = y;
        } else {
            a1 = y;
            b1 = focus;
        }
    } else if (!rand_edge(&a1, &b1)) {
        return 0;
    }
    if (!rand_edge(&a2, &b2)) return 0;
    if (a1 == a2 || b1 == b2) return 0;
    if (has_edge(a1, b2) || has_edge(a2, b1)) return 0;
    remove_edge(a1, b1);
    remove_edge(a2, b2);
    add_edge(a1, b2);
    add_edge(a2, b1);
    *oa1 = a1;
    *ob1 = b1;
    *oa2 = a2;
    *ob2 = b2;
    return 1;
}

static void undo_switch(int a1, int b1, int a2, int b2) {
    remove_edge(a1, b2);
    remove_edge(a2, b1);
    add_edge(a1, b1);
    add_edge(a2, b2);
}

/* Insert two new vertices (one per side) that take over the endpoints of
   k removed edges: degrees of old vertices are preserved. */
static int insert_pair(void) {
    if (n + 2 > maxn) return 0;
    int ea[64], eb[64];
    int k = 0;
    stamp++;
    for (int tr = 0; tr < 50 * d_ && k < d_; tr++) {
        int a, b;
        if (!rand_edge(&a, &b)) break;
        if (usedv[a] == stamp || usedv[b] == stamp) continue;
        usedv[a] = stamp;
        usedv[b] = stamp;
        ea[k] = a;
        eb[k] = b;
        k++;
    }
    if (k == 0) return 0;
    int w = n, w2 = n + 1;
    side[w] = 0;
    side[w2] = 1;
    deg[w] = 0;
    deg[w2] = 0;
    n += 2;
    for (int i = 0; i < k; i++) remove_edge(ea[i], eb[i]);
    for (int i = 0; i < k; i++) {
        add_edge(w, eb[i]);
        add_edge(w2, ea[i]);
    }
    return 1;
}

static void save_state(void) {
    snap_n = n;
    memcpy(snap_deg, deg, sizeof(int) * (size_t)n);
    memcpy(snap_nb, nb, sizeof(int) * (size_t)n * d_);
    have_snap = 1;
}

static void restore_state(void) {
    n = snap_n;
    memcpy(deg, snap_deg, sizeof(int) * (size_t)n);
    memcpy(nb, snap_nb, sizeof(int) * (size_t)n * d_);
}

/* Sampled cost on sources: identity when small, else bad vertices + random. */
static long refresh(void) {
    if (n <= KS) {
        ksrc = n;
        for (int j = 0; j < n; j++) src[j] = j;
    } else {
        ksrc = 0;
        for (int i = 0; i < nbad && ksrc < KS / 2; i++)
            if (badlist[i] < n) src[ksrc++] = badlist[i];
        while (ksrc < KS) src[ksrc++] = rndint(n);
    }
    return eval_src(src, ksrc, curbad);
}

/* Exact check over all sources. Returns 1 when every pair is within D_. */
static int exact_ok(void) {
    if (n <= KS) return 1;
    long c = eval_src(ident, n, tmpbad);
    if (c == 0) return 1;
    nbad = 0;
    for (int v = 0; v < n && nbad < maxn; v++)
        if (tmpbad[v] > 0) badlist[nbad++] = v;
    return 0;
}

static long sa_run(long cur, int steps) {
    for (int it = 0; it < steps && cur > 0; it++) {
        if (now_s() > deadline) break;
        double T = 0.6 * (1.0 - (double)it / (double)steps) + 0.05;
        int focus = -1;
        if (rnd01() < 0.5) {
            for (int tr = 0; tr < 30; tr++) {
                int x = rndint(n);
                if (curbad[x] > 0) {
                    focus = x;
                    break;
                }
            }
        }
        int a1, b1, a2, b2;
        if (!try_switch(&a1, &b1, &a2, &b2, focus)) continue;
        long c2 = eval_src(src, ksrc, candbad);
        if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
            memcpy(curbad, candbad, sizeof(int) * (size_t)n);
        } else {
            undo_switch(a1, b1, a2, b2);
        }
    }
    return cur;
}

static int grow(int k) {
    int c = 0;
    for (int i = 0; i < k; i++) {
        if (!insert_pair()) break;
        c++;
    }
    return c;
}

static int colour_graph(void) {
    for (int v = 0; v < n; v++) side[v] = -1;
    int *q = src;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[(size_t)u * d_ + i];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    q[tail++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: d D seed time [maxn]\n");
        return 1;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs = (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    maxn = argc > 5 ? atoi(argv[5]) : 16000;
    deadline = now_s() + tl;
    if (d_ < 1 || D_ < 1 || d_ > 64) {
        printf("0 0\n");
        return 0;
    }
    if (maxn < 2 * d_ + 8) maxn = 2 * d_ + 8;
    if (maxn > MAXN_CAP) maxn = MAXN_CAP;
    int Wc = (maxn + 63) >> 6;
    int srcsz = maxn > KS ? maxn : KS;
    bufA = malloc(sizeof(u64) * (size_t)maxn * Wc);
    bufB = malloc(sizeof(u64) * (size_t)maxn * Wc);
    side = malloc(sizeof(int) * (size_t)maxn);
    deg = calloc((size_t)maxn, sizeof(int));
    nb = calloc((size_t)maxn * d_, sizeof(int));
    curbad = calloc((size_t)maxn, sizeof(int));
    candbad = calloc((size_t)maxn, sizeof(int));
    tmpbad = calloc((size_t)maxn, sizeof(int));
    ident = calloc((size_t)maxn, sizeof(int));
    src = calloc((size_t)srcsz, sizeof(int));
    badlist = calloc((size_t)maxn, sizeof(int));
    snap_deg = calloc((size_t)maxn, sizeof(int));
    snap_nb = calloc((size_t)maxn * d_, sizeof(int));
    usedv = calloc((size_t)maxn, sizeof(int));
    if (!bufA || !bufB || !side || !deg || !nb || !curbad || !candbad || !tmpbad ||
        !ident || !src || !badlist || !snap_deg || !snap_nb || !usedv) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < maxn; i++) ident[i] = i;

    n = 0;
    int n0 = 0, m0 = 0, ok = 0;
    if (scanf("%d %d", &n0, &m0) == 2 && n0 >= 2 && n0 <= maxn - 2 && m0 >= 0) {
        n = n0;
        ok = 1;
        for (int e = 0; e < m0 && ok; e++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) {
                ok = 0;
                break;
            }
            if (u < 0 || v < 0 || u >= n || v >= n || u == v ||
                deg[u] >= d_ || deg[v] >= d_ || has_edge(u, v)) {
                ok = 0;
                break;
            }
            add_edge(u, v);
        }
        if (ok) ok = colour_graph();
    }
    if (!ok) {
        int h = d_ + 1;
        for (int i = 0; i < maxn; i++) deg[i] = 0;
        n = 2 * h;
        for (int v = 0; v < n; v++) side[v] = v < h ? 0 : 1;
        for (int i = 0; i < h; i++)
            for (int s = 0; s < d_; s++) add_edge(i, h + (i + s) % h);
        long iters = 20L * n * d_;
        int a1, b1, a2, b2;
        for (long it = 0; it < iters; it++) try_switch(&a1, &b1, &a2, &b2, -1);
    }

    long cur = refresh();
    int batch = 1;
    while (now_s() < deadline) {
        if (cur > 0) cur = sa_run(cur, STEPS);
        if (cur == 0) {
            if (exact_ok()) {
                save_state();
                if (batch < 1 + n / 100) batch *= 2;
                if (grow(batch) == 0) break;
            } else {
                cur = refresh();
                if (cur == 0) cur = 1;
                continue;
            }
        } else {
            if (!have_snap) continue;
            restore_state();
            if (batch > 1) batch /= 2;
            if (grow(batch) == 0) break;
        }
        cur = refresh();
    }

    if (!have_snap) {
        printf("0 0\n");
        return 0;
    }
    long m = 0;
    for (int a = 0; a < snap_n; a++)
        if (side[a] == 0) m += snap_deg[a];
    printf("%d %ld\n", snap_n, m);
    for (int a = 0; a < snap_n; a++) {
        if (side[a] != 0) continue;
        for (int i = 0; i < snap_deg[a]; i++)
            printf("%d %d\n", a, snap_nb[(size_t)a * d_ + i]);
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions (parent code).
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
# Bi-Cayley lift search over Z_m x| Z_k2 (parent code, used as the seed).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


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
    """Bitmask per vertex over the 2k block starts (left multiplication is an automorphism)."""
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


def _lift_phase(d, D, rng, deadline, floor_n):
    """Run the lift search until deadline; return the largest valid (n, edges) found, or None."""
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    found = None
    cur_n = floor_n

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        base = cur_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= cur_n:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            if res[0] > cur_n:
                found = res
                cur_n = res[0]
    return found


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    budget = max(0.5, min(0.85 * time_limit - 1.0, time_limit - 4.0))

    # Seed: a short lift search gives a structured valid start for the engine.
    try:
        found = _lift_phase(d, D, rng, t_start + 0.25 * budget, best[0])
        if found is not None:
            consider(found[0], found[1])
    except Exception:
        pass

    # Main: random-start / seeded bipartite search in C.
    left = budget - (time.monotonic() - t_start)
    if left > 1.0:
        maxn = min(lib.moore_bound(d, D) + 2, 20000)
        maxn = max(maxn, 2 * d + 8, best[0] + 4)
        start = best if best[0] > 2 * d else None
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{left - 0.5:.2f}", maxn],
                            stdin_graph=start, timeout=time_limit - 1.5)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
