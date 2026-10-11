import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact baselines (kept from the parent; they are cheap and always valid).
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


def _consider(best, n, e, d, D):
    """Return (n, e) if it is a valid graph larger than best, else best."""
    if n > best[0] and lib.is_valid(n, e, d, D):
        return (n, e)
    return best


# ----------------------------------------------------------------------------
# Group families. Each spec describes a finite group by a multiplication table.
# Lifts are bi-Cayley style: vertices A_{i,g}, B_{j,h} for i,j < K and g,h in G,
# dart (l, i) joins A_{i,g} to B_{P[l][i], g*S[l][i]}. The group may be
# non-abelian: this covers semidirect products Z_m x| Z_k, abelian Z_a x Z_b,
# affine groups GF(q) x| H (H a cyclic multiplier group, elementary abelian
# normal subgroup), and direct products with a small cyclic factor.
# ----------------------------------------------------------------------------

KF = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 20, 21, 24, 27, 28, 30, 32, 36, 40]
_GF_CACHE = {}


def _gf(q):
    if q not in _GF_CACHE:
        _GF_CACHE[q] = lib.GF(q)
    return _GF_CACHE[q]


def _rs_for(m, k):
    """All r in [2, m) with gcd(r, m) = 1 and r^k = 1 mod m."""
    if m < 3:
        return []
    return [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]


def _order(spec):
    kind = spec[0]
    if kind == "cyc":
        return spec[1]
    if kind in ("ab", "semi", "aff"):
        return spec[1] * spec[2]
    if kind == "prod":
        return _order(spec[1]) * _order(spec[2])
    raise ValueError(kind)


def _specs_for_order(G, rng):
    """Group specs of order G from several families."""
    specs = [("cyc", G)]
    for a in range(2, math.isqrt(G) + 1):
        if G % a == 0:
            b = G // a
            if math.gcd(a, b) > 1:  # non-cyclic abelian only
                specs.append(("ab", a, b))
    for k in KF:
        if G % k or G // k < 3:
            continue
        m = G // k
        rs = _rs_for(m, k)
        if rs:
            pick = rs if len(rs) <= 2 else rng.sample(rs, 2)
            for r in pick:
                specs.append(("semi", m, k, r))
    for q in range(2, min(G, 300) + 1):
        if G % q == 0 and lib.is_prime_power(q):
            h = G // q
            if h >= 2 and (q - 1) % h == 0:
                specs.append(("aff", q, h))
    for g2 in (2, 3, 5, 7):
        if G % g2 == 0 and G // g2 >= 3:
            g1 = G // g2
            for k in KF:
                if g1 % k == 0 and g1 // k >= 3:
                    m = g1 // k
                    rs = _rs_for(m, k)
                    if rs:
                        specs.append(("prod", ("semi", m, k, rs[0]), ("cyc", g2)))
                        break
    return specs


def _table(spec):
    """Multiplication table (G x G, int64) of the group described by spec. Identity is 0."""
    kind = spec[0]
    if kind == "cyc":
        m = spec[1]
        x = np.arange(m, dtype=np.int64)
        return (x[:, None] + x[None, :]) % m
    if kind == "ab":
        a, b = spec[1], spec[2]
        x = np.arange(a * b, dtype=np.int64)
        u, v = x // b, x % b
        return ((u[:, None] + u[None, :]) % a) * b + (v[:, None] + v[None, :]) % b
    if kind == "semi":
        m, k, r = spec[1], spec[2], spec[3]
        pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
        x = np.arange(m * k, dtype=np.int64)
        a, b = x // k, x % k
        return ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    if kind == "aff":
        q, h = spec[1], spec[2]
        F = _gf(q)
        prim = F.primitive_element()
        xs = np.array([F.pow(prim, t * ((q - 1) // h)) for t in range(h)], dtype=np.int64)
        G = q * h
        x = np.arange(G, dtype=np.int64)
        bc, t = x // h, x % h
        mulx = F.mul_table[xs[t][:, None], bc[None, :]]
        bres = F.add_table[bc[:, None], mulx]
        tres = (t[:, None] + t[None, :]) % h
        return bres * h + tres
    if kind == "prod":
        T1 = _table(spec[1])
        T2 = _table(spec[2])
        G1, G2 = T1.shape[0], T2.shape[0]
        out = T1.reshape(G1, 1, G1, 1) * G2 + T2.reshape(1, G2, 1, G2)
        return out.reshape(G1 * G2, G1 * G2)
    raise ValueError(kind)


# ----------------------------------------------------------------------------
# C engine: breakout local search over lifts with a supplied group table.
# The group table is given on stdin as a "graph" with n = |G| and m = |G|^2
# edges (x*|G|+y, x*y), i.e. the table in row-major order.
# argv: d D seed time_limit min_n kmask (bit0: K=1, bit1: K=2, bit2: K=3).
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXD 64
#define MAXK 3
#define PEN 1000
#define POLISH_T 80
#define STUCK 50
#define BREAK_ITERS 25000
#define SENTINEL 1000000000LL

typedef struct {
    int K, G;
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} Cfg;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 7, DD = 5;
static int G = 1;
static int *gtab = NULL;
static double deadline = 0.0;

static inline int gmul(int x, int y) { return gtab[x * G + y]; }

static int cap = 0;
static int *g_adj = NULL, *g_cnt = NULL, *g_vis = NULL, *g_q = NULL;
static long long *g_w = NULL;
static int g_stamp = 0;
static long long g_rawcost = 0;

static void ensure_cap(int N) {
    if (N <= cap) return;
    free(g_adj);
    free(g_cnt);
    free(g_vis);
    free(g_q);
    free(g_w);
    cap = N;
    g_adj = malloc(sizeof(int) * (size_t)N * (size_t)Dd);
    g_cnt = malloc(sizeof(int) * (size_t)N);
    g_vis = calloc((size_t)N, sizeof(int));
    g_q = malloc(sizeof(int) * (size_t)N);
    g_w = malloc(sizeof(long long) * (size_t)2 * MAXK * (size_t)N);
    if (!g_adj || !g_cnt || !g_vis || !g_q || !g_w) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    g_stamp = 0;
}

static void reset_weights(int K, int N) {
    long long total = (long long)2 * K * N;
    for (long long j = 0; j < total; j++) g_w[j] = 1;
}

/* Weighted cost (weights of unreached pairs + PEN * duplicate darts).
   Sets g_rawcost to the unweighted cost. If bump != 0, the weight of every
   currently unreached pair is increased by one. */
static long long cost_of(const Cfg *c, int bump) {
    int K = c->K, Gc = c->G, N = 2 * K * Gc;
    memset(g_cnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < Gc; g++) {
                int a = i * Gc + g;
                int b = (K + j) * Gc + gmul(g, s);
                if (g_cnt[a] >= Dd || g_cnt[b] >= Dd) {
                    g_rawcost = SENTINEL;
                    return SENTINEL;
                }
                g_adj[a * Dd + g_cnt[a]++] = b;
                g_adj[b * Dd + g_cnt[b]++] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;

    long long wsum = 0, raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * Gc;
        g_stamp++;
        int head = 0, tail = 0;
        g_vis[src] = g_stamp;
        g_q[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = g_q[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = g_adj[u * Dd + t];
                    if (g_vis[v] != g_stamp) {
                        g_vis[v] = g_stamp;
                        g_q[tail++] = v;
                    }
                }
            }
        }
        long long *w = g_w + (size_t)r * (size_t)N;
        for (int v = 0; v < N; v++) {
            if (g_vis[v] != g_stamp) {
                raw++;
                wsum += w[v];
                if (bump) w[v]++;
            }
        }
    }
    g_rawcost = raw + (long long)PEN * dup;
    return wsum + (long long)PEN * dup;
}

static void random_cfg(Cfg *c) {
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < c->K; i++) c->P[l][i] = i;
        for (int i = c->K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = c->P[l][i];
            c->P[l][i] = c->P[l][j];
            c->P[l][j] = t;
        }
        for (int i = 0; i < c->K; i++) c->S[l][i] = rint_(G);
    }
}

static long long breakout(Cfg *c, long iters) {
    long long wc = cost_of(c, 0);
    long long rc = g_rawcost;
    long long bestraw = rc;
    Cfg bc = *c;
    int stuck = 0;
    for (long t = 0; t < iters && wc != 0; t++) {
        if ((t & 127) == 0 && now_s() > deadline) break;
        int l = rint_(Dd);
        int i = rint_(c->K);
        int kind = (c->K >= 2 && rint_(4) == 0);
        int old_s = 0, i2 = 0;
        if (kind) {
            i2 = rint_(c->K - 1);
            if (i2 >= i) i2++;
            int tmp = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = tmp;
        } else {
            old_s = c->S[l][i];
            c->S[l][i] = rint_(G);
        }
        long long wc2 = cost_of(c, 0);
        if (wc2 <= wc) {
            if (wc2 < wc) stuck = 0;
            else stuck++;
            wc = wc2;
            rc = g_rawcost;
            if (rc < bestraw) {
                bestraw = rc;
                bc = *c;
            }
        } else {
            if (kind) {
                int tmp = c->P[l][i];
                c->P[l][i] = c->P[l][i2];
                c->P[l][i2] = tmp;
            } else {
                c->S[l][i] = old_s;
            }
            stuck++;
        }
        if (stuck >= STUCK) {
            cost_of(c, 1);
            wc = cost_of(c, 0);
            rc = g_rawcost;
            stuck = 0;
        }
    }
    *c = bc;
    return bestraw;
}

static long long polish(Cfg *c) {
    long long cost = cost_of(c, 0);
    int improved = 1;
    while (improved && cost != 0) {
        improved = 0;
        for (int l = 0; l < Dd && cost != 0; l++) {
            for (int i = 0; i < c->K; i++) {
                if (now_s() > deadline) return cost;
                int old = c->S[l][i];
                int bestv = old;
                long long bestc = cost;
                for (int s = 0; s < G; s++) {
                    if (s == old) continue;
                    c->S[l][i] = s;
                    long long c2 = cost_of(c, 0);
                    if (c2 < bestc) {
                        bestc = c2;
                        bestv = s;
                    }
                }
                c->S[l][i] = bestv;
                if (bestv != old) {
                    cost = bestc;
                    improved = 1;
                    if (cost == 0) break;
                }
            }
        }
    }
    return cost;
}

int main(int argc, char **argv) {
    double t0 = now_s();
    Dd = argc > 1 ? atoi(argv[1]) : 7;
    DD = argc > 2 ? atoi(argv[2]) : 5;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int min_n = argc > 5 ? atoi(argv[5]) : 0;
    int kmask = argc > 6 ? atoi(argv[6]) : 7;
    deadline = t0 + tl;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > 1200 || m != n * n) {
        printf("0 0\n");
        return 0;
    }
    gtab = malloc(sizeof(int) * (size_t)m);
    if (!gtab) {
        printf("0 0\n");
        return 0;
    }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || u >= m || v < 0 || v >= n) {
            printf("0 0\n");
            return 0;
        }
        gtab[u] = v;
    }
    G = n;

    int best_n = min_n;
    int have = 0;
    Cfg cur, best_cfg;
    memset(&cur, 0, sizeof(cur));
    memset(&best_cfg, 0, sizeof(best_cfg));

    while (now_s() < deadline) {
        int allowed[MAXK];
        int na = 0;
        for (int K = 1; K <= MAXK; K++) {
            if (!((kmask >> (K - 1)) & 1)) continue;
            if (2LL * K * G > best_n) allowed[na++] = K;
        }
        if (na == 0) break;
        int K = allowed[rint_(na)];
        int N = 2 * K * G;

        cur.K = K;
        cur.G = G;
        ensure_cap(N);
        random_cfg(&cur);
        reset_weights(K, N);
        breakout(&cur, BREAK_ITERS);
        cost_of(&cur, 0);
        if (g_rawcost > 0 && g_rawcost <= POLISH_T) {
            reset_weights(K, N);
            polish(&cur);
        }
        cost_of(&cur, 0);
        if (g_rawcost == 0) {
            best_n = N;
            best_cfg = cur;
            have = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    int K = best_cfg.K;
    int n_out = 2 * K * G;
    long m_out = (long)Dd * K * G;
    printf("%d %ld\n", n_out, m_out);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = best_cfg.P[l][i], s = best_cfg.S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + gmul(g, s));
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue.
# ----------------------------------------------------------------------------

PER_TASK = 2.5  # seconds of C search per group


def _group_search(d, D, seed, best, moore, deadline):
    """Run the C lift search over many groups in windows just above the target order."""
    floor_n = max(best[0], int(0.35 * moore))
    rng = random.Random(1000003 * seed + 97 * d + D)
    lists = {1: [], 2: [], 3: []}
    for K, width in ((1, 30), (2, 10), (3, 6)):
        lo = floor_n // (2 * K) + 1
        for G in range(lo, lo + width):
            if G < 2 or 2 * K * G > moore:
                continue
            for spec in _specs_for_order(G, rng):
                lists[K].append(spec)
        rng.shuffle(lists[K])
    tasks = [(1, s) for s in lists[1]] + [(2, s) for s in lists[2]] + [(3, s) for s in lists[3]]
    kmask = {1: 1, 2: 2, 3: 4}

    for K, spec in tasks:
        remaining = deadline - time.monotonic()
        tl = min(PER_TASK, remaining - 1.5)
        if tl < 1.0:
            break
        G = _order(spec)
        if 2 * K * G <= best[0]:
            continue
        try:
            T = _table(spec)
            G = T.shape[0]
            edges = list(zip(range(G * G), T.ravel().tolist()))
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{tl:.2f}", best[0], kmask[K]],
                            stdin_graph=(G, edges), timeout=tl + 3.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            continue
        best = _consider(best, n, e, d, D)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(3.0, min(0.88 * time_limit, time_limit - 5.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            best = _consider(best, pg[0], pg[1], d, D)
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            best = _consider(best, gq[0], gq[1], d, D)
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    if d >= 3 and D >= 3 and deadline - time.monotonic() > 4.0:
        try:
            best = _group_search(d, D, seed, best, moore, deadline)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
