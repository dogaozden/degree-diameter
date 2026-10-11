import itertools
import random
import time

import lib


C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int DEG, RAD, CAP, CAPW;
static double TL, T0;
static uint64_t RS;
static uint64_t *BUF1, *BUF2, *BUF3, *BUF4, *COV;
static int *GAIN, *USED, *OPT;
static int CH[256];

static uint64_t rnd64(void) {
    RS ^= RS << 13;
    RS ^= RS >> 7;
    RS ^= RS << 17;
    return RS;
}
static int rnd(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static double elapsed(void) { return now() - T0; }

typedef struct { int n; int *deg, *col, *adj; } G;

static G gnew(void) {
    G g;
    g.n = 0;
    g.deg = calloc((size_t)CAP, sizeof(int));
    g.col = calloc((size_t)CAP, sizeof(int));
    g.adj = calloc((size_t)CAP * DEG, sizeof(int));
    return g;
}

static void gcopy(G *dst, const G *src) {
    dst->n = src->n;
    memcpy(dst->deg, src->deg, sizeof(int) * (size_t)src->n);
    memcpy(dst->col, src->col, sizeof(int) * (size_t)src->n);
    memcpy(dst->adj, src->adj, sizeof(int) * (size_t)src->n * DEG);
}

static int has_edge(const G *g, int u, int v) {
    const int *a = g->adj + (size_t)u * DEG;
    for (int i = 0; i < g->deg[u]; i++)
        if (a[i] == v) return 1;
    return 0;
}

static void add_edge(G *g, int u, int v) {
    g->adj[(size_t)u * DEG + g->deg[u]++] = v;
    g->adj[(size_t)v * DEG + g->deg[v]++] = u;
}

static void del_one(G *g, int u, int v) {
    int *a = g->adj + (size_t)u * DEG;
    int k = g->deg[u];
    for (int i = 0; i < k; i++) {
        if (a[i] == v) {
            a[i] = a[k - 1];
            g->deg[u] = k - 1;
            return;
        }
    }
}

static void remove_edge(G *g, int u, int v) {
    del_one(g, u, v);
    del_one(g, v, u);
}

/* Bitset balls of radius r; result is in X or Y (returned). */
static uint64_t *balls(const G *g, int r, uint64_t *X, uint64_t *Y) {
    int n = g->n, W = (n + 63) >> 6;
    memset(X, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) X[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < r; t++) {
        for (int v = 0; v < n; v++) {
            uint64_t *y = Y + (size_t)v * W;
            const uint64_t *x = X + (size_t)v * W;
            memcpy(y, x, sizeof(uint64_t) * W);
            const int *a = g->adj + (size_t)v * DEG;
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *xu = X + (size_t)a[i] * W;
                for (int w = 0; w < W; w++) y[w] |= xu[w];
            }
        }
        uint64_t *tmp = X;
        X = Y;
        Y = tmp;
    }
    return X;
}

/* Number of unordered vertex pairs at distance > RAD. */
static long long cost(const G *g) {
    uint64_t *R = balls(g, RAD, BUF1, BUF2);
    int n = g->n, W = (n + 63) >> 6;
    long long cov = 0;
    size_t tot = (size_t)n * W;
    for (size_t i = 0; i < tot; i++) cov += __builtin_popcountll(R[i]);
    return ((long long)n * n - cov) / 2;
}

/* Greedy cover of all n vertices by balls R[s] of candidates on side c. */
static int greedy_cover(const G *g, const uint64_t *R, int W, int c, int randomize, int *chosen) {
    int n = g->n;
    memset(COV, 0, sizeof(uint64_t) * (size_t)W);
    for (int s = 0; s < n; s++) USED[s] = 0;
    int nc = 0;
    for (;;) {
        int pop = 0;
        for (int w = 0; w < W; w++) pop += __builtin_popcountll(COV[w]);
        if (pop == n || nc >= DEG) break;
        int best = 0;
        for (int s = 0; s < n; s++) {
            GAIN[s] = 0;
            if (USED[s] || g->col[s] != c || g->deg[s] >= DEG) continue;
            int gs = 0;
            const uint64_t *rs_ = R + (size_t)s * W;
            for (int w = 0; w < W; w++) gs += __builtin_popcountll(rs_[w] & ~COV[w]);
            GAIN[s] = gs;
            if (gs > best) best = gs;
        }
        if (best == 0) break;
        int thr = best;
        if (randomize && best > 1 && rnd(2) == 0) thr = best - 1;
        int no = 0;
        for (int s = 0; s < n; s++)
            if (GAIN[s] >= thr && GAIN[s] > 0) OPT[no++] = s;
        if (no == 0) break;
        int s = OPT[rnd(no)];
        USED[s] = 1;
        chosen[nc++] = s;
        const uint64_t *rr_ = R + (size_t)s * W;
        for (int w = 0; w < W; w++) COV[w] |= rr_[w];
    }
    int pop = 0;
    for (int w = 0; w < W; w++) pop += __builtin_popcountll(COV[w]);
    return pop == n ? nc : -1;
}

/* Add one vertex whose neighbourhood covers all vertices within RAD. */
static int grow_vertex(G *g) {
    int n = g->n;
    if (n + 1 >= CAP) return 0;
    int W = (n + 63) >> 6;
    uint64_t *R = balls(g, RAD - 1, BUF3, BUF4);
    int order[2] = {0, 1};
    if (rnd(2)) { order[0] = 1; order[1] = 0; }
    for (int oi = 0; oi < 2; oi++) {
        int c = order[oi];
        int nc = -1;
        for (int at = 0; at < 30 && nc < 0; at++)
            nc = greedy_cover(g, R, W, c, at > 0, CH);
        if (nc > 0) {
            int v = n;
            g->deg[v] = 0;
            g->col[v] = 1 - c;
            g->n = n + 1;
            for (int i = 0; i < nc; i++) add_edge(g, CH[i], v);
            return 1;
        }
    }
    return 0;
}

/* Add random cross-side edges between deficient vertices. */
static void saturate(G *g) {
    int n = g->n;
    int *L = malloc(sizeof(int) * (size_t)(n + 1));
    int *R = malloc(sizeof(int) * (size_t)(n + 1));
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] >= DEG) continue;
        if (g->col[v] == 0) L[nl++] = v;
        else R[nr++] = v;
    }
    if (nl > 0 && nr > 0) {
        size_t np = (size_t)nl * (size_t)nr;
        int *P = malloc(sizeof(int) * 2 * np);
        size_t k = 0;
        for (int a = 0; a < nl; a++)
            for (int b = 0; b < nr; b++) {
                P[2 * k] = L[a];
                P[2 * k + 1] = R[b];
                k++;
            }
        for (size_t i = np - 1; i > 0; i--) {
            size_t j = (size_t)rnd((int)(i + 1));
            int t0 = P[2 * i], t1 = P[2 * i + 1];
            P[2 * i] = P[2 * j];
            P[2 * i + 1] = P[2 * j + 1];
            P[2 * j] = t0;
            P[2 * j + 1] = t1;
        }
        for (size_t i = 0; i < np; i++) {
            int a = P[2 * i], b = P[2 * i + 1];
            if (g->deg[a] < DEG && g->deg[b] < DEG && !has_edge(g, a, b))
                add_edge(g, a, b);
        }
        free(P);
    }
    free(L);
    free(R);
}

static void grow(G *g) {
    for (int round = 0; round < 8; round++) {
        int before = g->n;
        while (grow_vertex(g)) { }
        saturate(g);
        if (g->n == before) break;
    }
}

/* Bipartite double-edge switches minimising bad pairs. Returns 1 if cost reaches 0. */
static int anneal(G *g, int iters) {
    int n = g->n;
    long long cur = cost(g);
    int *s0 = malloc(sizeof(int) * (size_t)(n + 1));
    int k0 = 0;
    for (int v = 0; v < n; v++)
        if (g->col[v] == 0) s0[k0++] = v;
    for (int it = 0; it < iters && cur > 0 && k0 > 1; it++) {
        if (elapsed() > TL) break;
        int a = s0[rnd(k0)];
        if (g->deg[a] == 0) continue;
        int b = g->adj[(size_t)a * DEG + rnd(g->deg[a])];
        int c = s0[rnd(k0)];
        if (c == a || g->deg[c] == 0) continue;
        int e = g->adj[(size_t)c * DEG + rnd(g->deg[c])];
        if (has_edge(g, a, e) || has_edge(g, c, b)) continue;
        remove_edge(g, a, b);
        remove_edge(g, c, e);
        add_edge(g, a, e);
        add_edge(g, c, b);
        long long nw = cost(g);
        if (nw <= cur || (nw == cur + 1 && rnd01() < 0.1)) {
            cur = nw;
        } else {
            remove_edge(g, a, e);
            remove_edge(g, c, b);
            add_edge(g, a, b);
            add_edge(g, c, e);
        }
    }
    free(s0);
    return cur == 0;
}

/* Copy src without killed vertices into dst (renumbered). */
static void kill_graph(const G *src, G *dst, const int *killed) {
    int n = src->n;
    int *map = malloc(sizeof(int) * (size_t)(n + 1));
    int m = 0;
    for (int v = 0; v < n; v++) map[v] = killed[v] ? -1 : m++;
    dst->n = m;
    for (int i = 0; i < m; i++) dst->deg[i] = 0;
    for (int v = 0; v < n; v++) {
        if (map[v] < 0) continue;
        dst->col[map[v]] = src->col[v];
        for (int i = 0; i < src->deg[v]; i++) {
            int u = src->adj[(size_t)v * DEG + i];
            if (map[u] >= 0 && v < u) add_edge(dst, map[v], map[u]);
        }
    }
    free(map);
}

/* Delete random edges while the diameter bound still holds. */
static void prune(G *g, int maxtests) {
    int n = g->n;
    int E = 0;
    for (int v = 0; v < n; v++)
        if (g->col[v] == 0) E += g->deg[v];
    int *eu = malloc(sizeof(int) * (size_t)(E + 1));
    int *ev = malloc(sizeof(int) * (size_t)(E + 1));
    int k = 0;
    for (int v = 0; v < n; v++) {
        if (g->col[v] != 0) continue;
        for (int i = 0; i < g->deg[v]; i++) {
            eu[k] = v;
            ev[k] = g->adj[(size_t)v * DEG + i];
            k++;
        }
    }
    for (int i = E - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t0 = eu[i], t1 = ev[i];
        eu[i] = eu[j];
        ev[i] = ev[j];
        eu[j] = t0;
        ev[j] = t1;
    }
    int tests = 0;
    for (int i = 0; i < E && tests < maxtests; i++) {
        if (elapsed() > TL) break;
        int u = eu[i], v = ev[i];
        if (!has_edge(g, u, v)) continue;
        tests++;
        remove_edge(g, u, v);
        if (cost(g) != 0) add_edge(g, u, v);
    }
    free(eu);
    free(ev);
}

/* Add one vertex greedily covering side `side`, removing edges from saturated neighbours. */
static void add_repair_vertex(G *g, int side) {
    int n = g->n;
    if (n + 1 >= CAP) return;
    int W = (n + 63) >> 6;
    uint64_t *R = balls(g, RAD - 1, BUF3, BUF4);
    memset(COV, 0, sizeof(uint64_t) * (size_t)W);
    for (int s = 0; s < n; s++) USED[s] = 0;
    int nc = 0;
    while (nc < DEG) {
        long long bestk = -1;
        int bs = -1;
        for (int s = 0; s < n; s++) {
            if (USED[s] || g->col[s] != side) continue;
            int gs = 0;
            const uint64_t *rs_ = R + (size_t)s * W;
            for (int w = 0; w < W; w++) gs += __builtin_popcountll(rs_[w] & ~COV[w]);
            long long key = (long long)gs * 2 + rnd(2);
            if (key > bestk) { bestk = key; bs = s; }
        }
        if (bs < 0) break;
        USED[bs] = 1;
        CH[nc++] = bs;
        const uint64_t *rb = R + (size_t)bs * W;
        for (int w = 0; w < W; w++) COV[w] |= rb[w];
    }
    int v = n;
    g->deg[v] = 0;
    g->col[v] = 1 - side;
    g->n = n + 1;
    for (int i = 0; i < nc; i++) {
        int s = CH[i];
        if (g->deg[s] >= DEG) {
            int t = g->adj[(size_t)s * DEG + rnd(g->deg[s])];
            remove_edge(g, s, t);
        }
        add_edge(g, s, v);
    }
}

static void bipartition(G *g) {
    int n = g->n;
    int *st = malloc(sizeof(int) * (size_t)(n + 1));
    for (int v = 0; v < n; v++) g->col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (g->col[s] != -1) continue;
        g->col[s] = 0;
        int sp = 0;
        st[sp++] = s;
        while (sp > 0) {
            int u = st[--sp];
            for (int i = 0; i < g->deg[u]; i++) {
                int v = g->adj[(size_t)u * DEG + i];
                if (g->col[v] == -1) {
                    g->col[v] = 1 - g->col[u];
                    st[sp++] = v;
                }
            }
        }
    }
    free(st);
}

int main(int argc, char **argv) {
    T0 = now();
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    TL = atof(argv[4]);
    RS = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (RS == 0) RS = 1;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 0) n0 = 0;
    if (m0 < 0) m0 = 0;
    if (d < 2 || d > 200 || D < 2) {
        printf("0 0\n");
        return 0;
    }
    int cap_e = m0 + d * d + 2;
    int *eu = malloc(sizeof(int) * (size_t)cap_e);
    int *ev = malloc(sizeof(int) * (size_t)cap_e);
    int ne = 0;
    for (int i = 0; i < m0; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a < 0 || b < 0 || a >= n0 || b >= n0 || a == b) continue;
        eu[ne] = a;
        ev[ne] = b;
        ne++;
    }
    if (n0 == 0) {
        n0 = 2 * d;
        ne = 0;
        for (int i = 0; i < d; i++)
            for (int j = 0; j < d; j++) {
                eu[ne] = i;
                ev[ne] = d + j;
                ne++;
            }
    }

    double sum = 0.0, pw = 1.0;
    for (int i = 0; i < D; i++) {
        sum += pw;
        pw *= (double)(d - 1);
    }
    double moore = 2.0 * sum;
    double capd = moore < 8000.0 ? moore : 8000.0;
    CAP = (int)capd + 4;
    if (CAP < n0 + 4) CAP = n0 + 4;
    DEG = d;
    RAD = D;
    CAPW = (CAP + 63) / 64;
    size_t bsz = (size_t)CAP * CAPW + 1;
    BUF1 = malloc(sizeof(uint64_t) * bsz);
    BUF2 = malloc(sizeof(uint64_t) * bsz);
    BUF3 = malloc(sizeof(uint64_t) * bsz);
    BUF4 = malloc(sizeof(uint64_t) * bsz);
    COV = malloc(sizeof(uint64_t) * (size_t)(CAPW + 1));
    GAIN = malloc(sizeof(int) * (size_t)CAP);
    USED = malloc(sizeof(int) * (size_t)CAP);
    OPT = malloc(sizeof(int) * (size_t)CAP);

    G start = gnew(), cur = gnew(), best = gnew(), work = gnew(), cand = gnew();
    start.n = n0;
    for (int v = 0; v < n0; v++) start.deg[v] = 0;
    for (int i = 0; i < ne; i++) {
        int a = eu[i], b = ev[i];
        if (start.deg[a] < DEG && start.deg[b] < DEG && !has_edge(&start, a, b))
            add_edge(&start, a, b);
    }
    bipartition(&start);
    gcopy(&best, &start);
    gcopy(&cur, &start);
    grow(&cur);
    if (cur.n > best.n && cost(&cur) == 0) gcopy(&best, &cur);
    int bestn = best.n;

    int *killflag = malloc(sizeof(int) * (size_t)CAP);
    static const int KS[6] = {1, 1, 2, 2, 3, 4};

    while (elapsed() < TL) {
        int r = rnd(10);
        if (r < 6) {
            gcopy(&work, &cur);
            int kc = KS[rnd(6)];
            if (kc >= work.n) continue;
            memset(killflag, 0, sizeof(int) * (size_t)work.n);
            for (int i = 0; i < kc;) {
                int v = rnd(work.n);
                if (!killflag[v]) {
                    killflag[v] = 1;
                    i++;
                }
            }
            kill_graph(&work, &cand, killflag);
            saturate(&cand);
            if (!anneal(&cand, 150)) continue;
            grow(&cand);
        } else if (r < 8) {
            gcopy(&work, &cur);
            add_repair_vertex(&work, rnd(2));
            saturate(&work);
            if (!anneal(&work, 1000)) continue;
            grow(&work);
            gcopy(&cand, &work);
        } else {
            gcopy(&work, &cur);
            prune(&work, 160);
            grow(&work);
            gcopy(&cand, &work);
        }
        int cn = cand.n;
        if (cn > bestn && cost(&cand) == 0) {
            gcopy(&best, &cand);
            bestn = cn;
        }
        if (cn >= cur.n - 1) gcopy(&cur, &cand);
        else if (cn < bestn - 3 || rnd(20) == 0) gcopy(&cur, &best);
    }

    int bn = best.n;
    long long tot = 0;
    for (int v = 0; v < bn; v++) tot += best.deg[v];
    printf("%d %lld\n", bn, tot / 2);
    for (int v = 0; v < bn; v++)
        for (int i = 0; i < best.deg[v]; i++) {
            int u = best.adj[(size_t)v * DEG + i];
            if (v < u) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q) (order 2(q+1)(q^2+1))."""
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
    """W(q) for the largest prime power q <= 9 with q + 1 <= d (kept small for speed)."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python helpers (growth, twins, and a fallback search if C is unavailable).
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
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
    return color


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _greedy_cover(cands, ball, full, d, rng, randomize):
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(30):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Join deficient opposite-side vertices at random (keeps validity)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _duplicate_twins(n, edges, d, rng):
    """Add non-adjacent twins (same neighbourhood) while neighbours have spare degree."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    changed = True
    while changed:
        changed = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d:
                continue
            if any(len(adj[u]) >= d for u in nb):
                continue
            w = len(adj)
            adj.append(set(nb))
            for u in nb:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def _cost(adj, D):
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _fill(adj, color, d, rng):
    n = len(adj)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _anneal(adj, color, d, D, rng, iters, deadline):
    """Degree-preserving bipartite switches minimising bad pairs. True if cost reaches 0."""
    cur = _cost(adj, D)
    side0 = [v for v in range(len(adj)) if color[v] == 0]
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        a = rng.choice(side0)
        if not adj[a]:
            continue
        b = rng.choice(tuple(adj[a]))
        c = rng.choice(side0)
        if c == a or not adj[c]:
            continue
        e = rng.choice(tuple(adj[c]))
        if e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _cost(adj, D)
        if new <= cur or (new == cur + 1 and rng.random() < 0.1):
            cur = new
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return cur == 0


def _lns(n, edges, d, D, deadline, rng, consider):
    """Kill-repair-regrow search from a valid graph (Python fallback)."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 2, 3, 4))
        if k >= cur_n:
            break
        kill = set(rng.sample(range(cur_n), k))
        keep = [v for v in range(cur_n) if v not in kill]
        remap = {v: i for i, v in enumerate(keep)}
        m = len(keep)
        e2 = [(remap[u], remap[v]) for u, v in cur_e if u not in kill and v not in kill]
        adj = _to_sets(m, e2)
        color = _bipartition(m, adj)
        _fill(adj, color, d, rng)
        if not _anneal(adj, color, d, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(m) for v in adj[u] if u < v]
        n4, e4 = _grow(m, e3, d, D, deadline, rng)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Entry point: structured base and twins in Python, then the C engine
# (kill-repair-regrow, add-repair, and redundant-edge pruning), then a
# Python fallback for any leftover time or if the C run fails.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.9 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if best_n >= moore:
        return best_n, list(best_e)

    # Structured base: W(q) for D >= 4, PG(2,q) for D = 3.
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.15 * time_limit, rng)
            consider(n1, e1)

    if best_n >= moore:
        return best_n, list(best_e)

    # Twin duplication, saturation and growth (cheap, usually adds vertices).
    nt, et = _duplicate_twins(best_n, best_e, d, rng)
    et = _saturate_edges(nt, et, d, rng)
    nt, et = _grow(nt, et, d, D, start + 0.2 * time_limit, rng)
    consider(nt, et)

    # C engine: most of the budget.
    if D >= 2 and time_limit >= 10:
        c_budget = 0.85 * time_limit - (time.monotonic() - start) - 4.0
        if c_budget >= 4.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=(best_n, best_e), timeout=c_budget + 10.0)
                cn, ce = lib.parse_graph_text(text)
                consider(cn, ce)
            except Exception:
                pass

    # Python fallback for any remaining time (or if the C run failed).
    if D >= 2 and time.monotonic() < deadline:
        _lns(best_n, best_e, d, D, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
