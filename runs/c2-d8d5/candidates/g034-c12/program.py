import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine 1: voltage-lift annealer over Z_m x| Z_k2 with k blocks per side.
#
# Vertex (side 0, block i, element x) is i*G+x; (side 1, block j, element y) is
# (k+j)*G+y. Dart l of block i joins it to block perm[l][i] with voltage S[l][i]:
# (0,i,x) ~ (1,perm[l][i], x*s). Every vertex then has degree d. Left
# translation by the group is an automorphism, so the diameter is at most D
# iff the 2k block representatives reach every vertex within D steps. The cost
# is that unreached count plus 1000 per duplicate dart.
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, m_, k2_, G_, N_;
static int *pw, *perm, *invp, *S, *nbr, *vis, *que;
static int stamp_ = 0;

static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_, c = y / k2_, e = y % k2_;
    long long t = (a + (long long)pw[b] * c) % m_;
    return (int)(t * k2_ + (b + e) % k2_);
}

static int ginv(int x) {
    int a = x / k2_, b = x % k2_;
    int nb = (k2_ - b) % k2_;
    long long t = (m_ - ((long long)pw[nb] * a) % m_) % m_;
    return (int)(t * k2_ + nb);
}

static void set_invp(int l) {
    for (int i = 0; i < k_; i++) invp[l * k_ + perm[l * k_ + i]] = i;
}

static void rebuild(void) {
    for (int i = 0; i < k_; i++)
        for (int x = 0; x < G_; x++) {
            int v = i * G_ + x;
            for (int l = 0; l < d_; l++) {
                int j = perm[l * k_ + i];
                int s = S[l * k_ + i];
                nbr[v * d_ + l] = (k_ + j) * G_ + gmul(x, s);
            }
        }
    for (int j = 0; j < k_; j++)
        for (int y = 0; y < G_; y++) {
            int v = (k_ + j) * G_ + y;
            for (int l = 0; l < d_; l++) {
                int i = invp[l * k_ + j];
                int s = S[l * k_ + i];
                nbr[v * d_ + l] = i * G_ + gmul(y, ginv(s));
            }
        }
}

static long long unreached(int src) {
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int dep = 0; dep < D_; dep++) {
        if (head == tail) break;
        int end = tail;
        while (head < end) {
            int v = que[head++];
            for (int l = 0; l < d_; l++) {
                int u = nbr[v * d_ + l];
                if (vis[u] != stamp_) {
                    vis[u] = stamp_;
                    que[tail++] = u;
                }
            }
        }
    }
    return (long long)(N_ - tail);
}

static int dups(void) {
    int c = 0;
    for (int i = 0; i < k_; i++)
        for (int l1 = 0; l1 < d_; l1++)
            for (int l2 = l1 + 1; l2 < d_; l2++)
                if (perm[l1 * k_ + i] == perm[l2 * k_ + i] && S[l1 * k_ + i] == S[l2 * k_ + i]) c++;
    return c;
}

static long long cost_all(void) {
    long long c = 0;
    for (int i = 0; i < k_; i++) c += unreached(i * G_);
    for (int j = 0; j < k_; j++) c += unreached((k_ + j) * G_);
    c += 1000LL * (long long)dups();
    return c;
}

static void emit(void) {
    printf("%d %d\n", N_, d_ * k_ * G_);
    for (int i = 0; i < k_; i++)
        for (int x = 0; x < G_; x++)
            for (int l = 0; l < d_; l++) {
                int j = perm[l * k_ + i];
                int s = S[l * k_ + i];
                printf("%d %d\n", i * G_ + x, (k_ + j) * G_ + gmul(x, s));
            }
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    m_ = atoi(argv[5]);
    k2_ = atoi(argv[6]);
    long long r = atoll(argv[7]);
    k_ = atoi(argv[8]);
    if (d_ < 1 || D_ < 1 || m_ < 1 || k2_ < 1 || k_ < 1 || k2_ > 1000 || k_ > 64) {
        printf("0 0\n");
        return 0;
    }
    G_ = m_ * k2_;
    if (G_ > 200000 || 2LL * k_ * G_ > 400000) { printf("0 0\n"); return 0; }
    N_ = 2 * k_ * G_;

    pw = malloc(sizeof(int) * (size_t)k2_);
    perm = malloc(sizeof(int) * (size_t)d_ * k_);
    invp = malloc(sizeof(int) * (size_t)d_ * k_);
    S = malloc(sizeof(int) * (size_t)d_ * k_);
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    vis = calloc((size_t)N_, sizeof(int));
    que = malloc(sizeof(int) * (size_t)N_);
    int *tmp = malloc(sizeof(int) * (size_t)k_);
    if (!pw || !perm || !invp || !S || !nbr || !vis || !que || !tmp) { printf("0 0\n"); return 0; }

    /* powers of r; r^k2 must be 1 mod m */
    long long rr = ((r % m_) + m_) % m_;
    long long cur_p = 1 % m_;
    for (int b = 0; b < k2_; b++) {
        pw[b] = (int)cur_p;
        cur_p = cur_p * rr % m_;
    }
    if (cur_p != 1 % m_) { printf("0 0\n"); return 0; }

    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int t = 0; t < 10; t++) rnd();

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) tmp[i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = tmp[i]; tmp[i] = tmp[j]; tmp[j] = t;
        }
        for (int i = 0; i < k_; i++) perm[l * k_ + i] = tmp[i];
        set_invp(l);
        for (int i = 0; i < k_; i++) S[l * k_ + i] = rint_(G_);
    }

    rebuild();
    long long cur = cost_all();
    if (cur == 0) { emit(); return 0; }

    clock_t c0 = clock();
    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = 30.0 * pow(0.3 / 30.0, el / limit);

        if (k_ >= 2 && rdbl() < 0.3) {
            int l = rint_(d_);
            int i1 = rint_(k_), i2 = rint_(k_ - 1);
            if (i2 >= i1) i2++;
            int *p = &perm[l * k_];
            int t = p[i1]; p[i1] = p[i2]; p[i2] = t;
            set_invp(l);
            rebuild();
            long long nc = cost_all();
            if (nc <= cur || rdbl() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                t = p[i1]; p[i1] = p[i2]; p[i2] = t;
                set_invp(l);
                rebuild();
            }
        } else {
            if (G_ < 2) continue;
            int l = rint_(d_), i = rint_(k_);
            int *s = &S[l * k_ + i];
            int old = *s;
            int nw = rint_(G_ - 1);
            if (nw >= old) nw++;
            *s = nw;
            rebuild();
            long long nc = cost_all();
            if (nc <= cur || rdbl() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                *s = old;
                rebuild();
            }
        }
        if (cur == 0) { emit(); return 0; }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: bipartite edge-toggle annealer with vertex growth (from parent).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, cap_n, cap_w, N, W;
static int *deg, *adj, *side, *bestEu, *bestEv;
static u64 *bufA, *bufB;
static int *bvCur, *bvNew;
static int best_n = 0, best_m = 0;

static int isadj(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a * d_ + i] == b) return 1;
    return 0;
}
static void delE1(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a * d_ + i] == b) {
            adj[a * d_ + i] = adj[a * d_ + deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}
static void addE(int a, int b) {
    adj[a * d_ + deg[a]++] = b;
    adj[b * d_ + deg[b]++] = a;
}
static void delE(int a, int b) { delE1(a, b); delE1(b, a); }

static long long bad_pairs(int *out) {
    u64 *cur = bufA, *alt = bufB;
    W = (N + 63) / 64;
    memset(cur, 0, sizeof(u64) * (size_t)N * (size_t)cap_w);
    for (int v = 0; v < N; v++) cur[(size_t)v * cap_w + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 *x = alt + (size_t)v * cap_w;
            u64 *r = cur + (size_t)v * cap_w;
            for (int w = 0; w < W; w++) x[w] = r[w];
            for (int i = 0; i < deg[v]; i++) {
                u64 *q = cur + (size_t)adj[v * d_ + i] * cap_w;
                for (int w = 0; w < W; w++) x[w] |= q[w];
            }
            for (int w = 0; w < W; w++) if (x[w] != r[w]) changed = 1;
        }
        u64 *t = cur; cur = alt; alt = t;
        if (!changed) break;
    }
    long long total = 0;
    for (int v = 0; v < N; v++) {
        u64 *r = cur + (size_t)v * cap_w;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += __builtin_popcountll(r[w]);
        out[v] = N - pc;
        total += out[v];
    }
    return total;
}

static int pick_vertex(void) {
    if (rdbl() < 0.5) {
        for (int t = 0; t < 8; t++) {
            int v = rint_(N);
            if (bvCur[v] > 0) return v;
        }
    }
    return rint_(N);
}

static void save_best(void) {
    int m = 0;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v * d_ + i];
            if (u > v) { bestEu[m] = v; bestEv[m] = u; m++; }
        }
    }
    best_n = N;
    best_m = m;
}

static void grow_pair(void) {
    side[N] = 0; deg[N] = 0;
    side[N + 1] = 1; deg[N + 1] = 0;
    N += 2;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    int grow_max = argc > 5 ? atoi(argv[5]) : 60;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (d_ < 1 || D_ < 1 || n0 < 2 || n0 > 1000000 || grow_max < 0) {
        printf("0 0\n");
        return 0;
    }
    cap_n = n0 + 2 * grow_max + 2;
    cap_w = (cap_n + 63) / 64;
    deg = calloc(cap_n, sizeof(int));
    side = malloc(sizeof(int) * (size_t)cap_n);
    adj = malloc(sizeof(int) * (size_t)cap_n * d_);
    bestEu = malloc(sizeof(int) * (size_t)cap_n * d_);
    bestEv = malloc(sizeof(int) * (size_t)cap_n * d_);
    bufA = malloc(sizeof(u64) * (size_t)cap_n * cap_w);
    bufB = malloc(sizeof(u64) * (size_t)cap_n * cap_w);
    bvCur = malloc(sizeof(int) * (size_t)cap_n);
    bvNew = malloc(sizeof(int) * (size_t)cap_n);
    if (!deg || !side || !adj || !bestEu || !bestEv || !bufA || !bufB || !bvCur || !bvNew) {
        printf("0 0\n");
        return 0;
    }

    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (deg[u] >= d_ || deg[v] >= d_ || isadj(u, v)) continue;
        addE(u, v);
    }

    for (int v = 0; v < N; v++) side[v] = -1;
    int *q = malloc(sizeof(int) * (size_t)cap_n);
    for (int s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v * d_ + i];
                if (side[u] == -1) { side[u] = 1 - side[v]; q[t++] = u; }
            }
        }
    }
    free(q);

    const double T0 = 30.0, T1 = 0.3;
    clock_t c0 = clock();
    long long cost = bad_pairs(bvCur);
    if (cost == 0 && N > best_n) {
        save_best();
        if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(bvCur); }
    }

    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double frac = el / limit;
        double T = T0 * pow(T1 / T0, frac);

        int a = -1, b = -1;
        for (int t = 0; t < 50; t++) {
            int x = pick_vertex(), y = pick_vertex();
            if (x == y || side[x] == side[y] || isadj(x, y)) continue;
            a = x; b = y;
            break;
        }
        if (a < 0) continue;

        int xa = -1, xb = -1;
        if (deg[a] == d_) { xa = adj[a * d_ + rint_(deg[a])]; delE(a, xa); }
        if (deg[b] == d_) { xb = adj[b * d_ + rint_(deg[b])]; delE(b, xb); }
        addE(a, b);

        long long nc = bad_pairs(bvNew);
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
            int *tp = bvCur; bvCur = bvNew; bvNew = tp;
            if (cost == 0 && N > best_n) {
                save_best();
                if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(bvCur); }
            }
        } else {
            delE(a, b);
            if (xa >= 0) addE(a, xa);
            if (xb >= 0) addE(b, xb);
        }
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestEu[i], bestEv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bipartition(n, adj):
    """2-colouring of the graph, or None if it is not bipartite."""
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
    """Greedily add vertices using spare degree; returns a valid (n, edges)."""
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
                cand = edges + [(v, n) for v in pick]
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


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """Run the edge-toggle C annealer from a valid graph; returns parsed output (may be (0, []))."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


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


# ----------------------------------------------------------------------------
# Phase A: C voltage-lift search over semidirect groups (new construction).
# ----------------------------------------------------------------------------

def _lift_phase(d, D, rng, deadline, get_n, consider):
    """Repeatedly anneal lifts over random groups, each slightly larger than the current best."""
    while True:
        rem = deadline - time.monotonic()
        if rem < 1.5:
            break
        k = rng.choice([2, 2, 3, 3, 4, 5, 6])
        n_best = get_n()
        gmin = n_best // (2 * k) + 1
        target = gmin + rng.randrange(0, gmin // 30 + 2)
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= n_best:
            continue
        sec = min(rem - 0.5, max(2.0, min(10.0, 0.35 * rem)))
        if sec < 1.0:
            break
        try:
            out = lib.run_c(C_LIFT, [d, D, rng.randrange(1, 1 << 30), f"{sec:.2f}", m, k2, r, k],
                            timeout=sec + 15.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            continue
        if n > 0:
            consider(n, e)


# ----------------------------------------------------------------------------
# Phase B: Python bi-Cayley annealing over semidirect products (parent method).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 with element a*k2+b."""
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
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
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
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing over voltages and layer permutations. Returns (n, edges) or None."""
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


# ----------------------------------------------------------------------------
# Driver. Phases, as fractions of time_limit:
#   A  0.00-0.45  C voltage-lift search (new)
#   B  0.45-0.75  Python bi-Cayley annealing (parent)
#   C  0.75-0.88  C edge-toggle growth from the best graph (parent)
#   D  0.88-0.93  greedy slack extension
# Every phase only replaces the best graph with a validated one.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    T = float(time_limit)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Phase A: voltage lifts over semidirect groups.
    try:
        _lift_phase(d, D, rng, t0 + 0.45 * T, lambda: best[0], consider)
    except Exception:
        pass

    # Phase B: Python bi-Cayley annealing (parent method), with a bandit over base sizes.
    try:
        py_end = t0 + 0.75 * T
        trials = {k: 0 for k in _KS}
        wins = {k: 0 for k in _KS}

        def pick_k():
            if rng.random() < 0.2:
                return rng.choice(_KS)
            return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

        while time.monotonic() < py_end:
            k = pick_k()
            base = best[0] // (2 * k)
            target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
            g = _sample_group(target, rng)
            if g is None:
                continue
            m, k2, r = g
            G, Ts, Invs = _semidirect_tables(m, k2, r)
            if 2 * k * G <= best[0]:
                continue
            trials[k] += 1
            res = _search(d, D, k, G, Ts, Invs, rng, py_end, 4000, 1200)
            if res is not None:
                wins[k] += 1
                consider(res[0], res[1])
    except Exception:
        pass

    # Phase C: C edge-toggle annealer grows the best valid graph by vertex pairs.
    try:
        grow_budget = t0 + 0.88 * T - time.monotonic()
        if grow_budget >= 1.5:
            cn, ce = _grow_in_c(best[0], best[1], d, D, grow_budget,
                                rng.randrange(1, 1 << 30), 200)
            consider(cn, ce)
    except Exception:
        pass

    # Phase D: greedy slack extension.
    try:
        slack_end = t0 + 0.93 * T
        if time.monotonic() < slack_end - 0.5:
            n2, e2 = _slack_extend(best[0], best[1], d, D, rng, slack_end)
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
