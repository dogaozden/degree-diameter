import itertools
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define CAP 4096
#define WMAX (CAP / 64)

static int DEG, DIST;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
#if defined(__GNUC__)
    return __builtin_popcountll(x);
#else
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
#endif
}

static int n;
static int col[CAP];
static int deg[CAP];
static int *nb;
static unsigned char *A;
static uint64_t *ballA, *ballB;

#define AD(u, v) A[(size_t)(u) * CAP + (v)]
#define NB(v, i) nb[(size_t)(v) * DEG + (i)]

static void add_edge(int u, int v) {
    AD(u, v) = 1; AD(v, u) = 1;
    NB(u, deg[u]) = v; deg[u]++;
    NB(v, deg[v]) = u; deg[v]++;
}

static void rem_nb(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (NB(u, i) == v) {
            NB(u, i) = NB(u, deg[u] - 1);
            deg[u]--;
            return;
        }
    }
}

static void del_edge(int u, int v) {
    AD(u, v) = 0; AD(v, u) = 0;
    rem_nb(u, v); rem_nb(v, u);
}

/* Replace the current graph by nn vertices, edges (eu,ev), sides c. */
static void set_graph(int nn, int m, const int *eu, const int *ev, const int *c) {
    for (int i = 0; i < n; i++) {
        memset(&A[(size_t)i * CAP], 0, (size_t)n);
        deg[i] = 0;
    }
    n = nn;
    for (int i = 0; i < n; i++) col[i] = c[i];
    for (int i = 0; i < m; i++) add_edge(eu[i], ev[i]);
}

typedef struct { int n, m; int *eu, *ev, *col; } Snap;

static Snap snap_new(void) {
    Snap s;
    s.n = 0; s.m = 0;
    s.eu = malloc(sizeof(int) * (size_t)CAP * DEG);
    s.ev = malloc(sizeof(int) * (size_t)CAP * DEG);
    s.col = malloc(sizeof(int) * CAP);
    return s;
}

static void snap_take(Snap *s) {
    int m = 0;
    for (int v = 0; v < n; v++)
        for (int i = 0; i < deg[v]; i++) {
            int u = NB(v, i);
            if (v < u) { s->eu[m] = v; s->ev[m] = u; m++; }
        }
    s->n = n; s->m = m;
    memcpy(s->col, col, sizeof(int) * n);
}

static void snap_load(const Snap *s) {
    set_graph(s->n, s->m, s->eu, s->ev, s->col);
}

static void snap_copy(Snap *dst, const Snap *src) {
    dst->n = src->n; dst->m = src->m;
    memcpy(dst->eu, src->eu, sizeof(int) * (size_t)src->m);
    memcpy(dst->ev, src->ev, sizeof(int) * (size_t)src->m);
    memcpy(dst->col, src->col, sizeof(int) * (size_t)src->n);
}

/* ballA = bitmask of vertices within distance r of each vertex. */
static void compute_ball(int r) {
    int W = (n + 63) / 64;
    memset(ballA, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++)
        ballA[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int t = 0; t < r; t++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = &ballB[(size_t)v * W];
            memcpy(dst, &ballA[(size_t)v * W], sizeof(uint64_t) * W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = &ballA[(size_t)NB(v, i) * W];
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        memcpy(ballA, ballB, sizeof(uint64_t) * (size_t)n * W);
    }
}

/* Number of unordered pairs at distance > DIST. */
static long cost(void) {
    int W = (n + 63) / 64;
    long bad = 0;
    compute_ball(DIST);
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(ballA[(size_t)v * W + w]);
        bad += n - c;
    }
    return bad / 2;
}

static int cands_buf[CAP], pool_buf[CAP], chosen_buf[256];
static int gain_buf[CAP], opt_buf[CAP];

/* ballA holds radius DIST-1 balls. Greedy cover of all n vertices by <= DEG candidates.
   Returns number chosen (>0) or -1 on failure. */
static int greedy_cover(const int *cands, int nc, int randomize) {
    int W = (n + 63) / 64;
    uint64_t cov[WMAX], full[WMAX];
    memset(cov, 0, sizeof cov);
    memset(full, 0, sizeof full);
    for (int v = 0; v < n; v++) full[v / 64] |= 1ULL << (v % 64);
    int np = nc;
    memcpy(pool_buf, cands, sizeof(int) * nc);
    if (randomize) {
        for (int i = np - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = pool_buf[i]; pool_buf[i] = pool_buf[j]; pool_buf[j] = t;
        }
    }
    int nch = 0;
    for (;;) {
        int done = 1;
        for (int w = 0; w < W; w++) if (cov[w] != full[w]) { done = 0; break; }
        if (done) return nch;
        if (nch >= DEG || np == 0) return -1;
        int best = 0;
        for (int i = 0; i < np; i++) {
            int g = 0;
            const uint64_t *b = &ballA[(size_t)pool_buf[i] * W];
            for (int w = 0; w < W; w++) g += popc(b[w] & ~cov[w]);
            gain_buf[i] = g;
            if (g > best) best = g;
        }
        if (best == 0) return -1;
        int thr = best;
        if (randomize && rndint(2)) thr = best - 1;
        int no = 0;
        for (int i = 0; i < np; i++)
            if (gain_buf[i] >= thr && gain_buf[i] > 0) opt_buf[no++] = i;
        int pick = randomize ? opt_buf[rndint(no)] : opt_buf[0];
        int s = pool_buf[pick];
        chosen_buf[nch++] = s;
        for (int w = 0; w < W; w++) cov[w] |= ballA[(size_t)s * W + w];
        pool_buf[pick] = pool_buf[np - 1];
        np--;
    }
}

/* Add one vertex joined to a cover of the opposite side. Returns 1 if added. */
static int try_grow(void) {
    if (n >= CAP - 1) return 0;
    compute_ball(DIST - 1);
    int order[2] = {0, 1};
    if (rndint(2)) { order[0] = 1; order[1] = 0; }
    for (int oi = 0; oi < 2; oi++) {
        int c = order[oi];
        int nc = 0;
        for (int v = 0; v < n; v++)
            if (col[v] == c && deg[v] < DEG) cands_buf[nc++] = v;
        if (nc == 0) continue;
        for (int att = 0; att < 16; att++) {
            int k = greedy_cover(cands_buf, nc, att > 0);
            if (k > 0) {
                int v = n;
                n++;
                col[v] = 1 - c;
                deg[v] = 0;
                for (int i = 0; i < k; i++) add_edge(chosen_buf[i], v);
                return 1;
            }
        }
    }
    return 0;
}

static int *pa_buf = NULL, *pb_buf = NULL, *L_buf = NULL, *R_buf = NULL;

/* Add cross-side edges between deficient vertices in random order. */
static void fill(void) {
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] >= DEG) continue;
        if (col[v] == 0) L_buf[nl++] = v; else R_buf[nr++] = v;
    }
    int cnt = 0;
    for (int i = 0; i < nl; i++)
        for (int j = 0; j < nr; j++) {
            int a = L_buf[i], b = R_buf[j];
            if (!AD(a, b)) { pa_buf[cnt] = a; pb_buf[cnt] = b; cnt++; }
        }
    for (int i = cnt - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = pa_buf[i]; pa_buf[i] = pa_buf[j]; pa_buf[j] = t;
        t = pb_buf[i]; pb_buf[i] = pb_buf[j]; pb_buf[j] = t;
    }
    for (int i = 0; i < cnt; i++) {
        int a = pa_buf[i], b = pb_buf[i];
        if (deg[a] < DEG && deg[b] < DEG && !AD(a, b)) add_edge(a, b);
    }
}

static int *s0_buf = NULL;

/* Bipartite double-edge switches minimising bad pairs. Returns final cost. */
static long anneal(int iters, double t_end) {
    long cur = cost();
    int ns0 = 0;
    for (int v = 0; v < n; v++) if (col[v] == 0) s0_buf[ns0++] = v;
    if (ns0 < 2) return cur;
    for (int it = 0; it < iters && cur != 0; it++) {
        if ((it & 15) == 0 && now() > t_end) break;
        int a = s0_buf[rndint(ns0)];
        if (deg[a] == 0) continue;
        int b = NB(a, rndint(deg[a]));
        int c = s0_buf[rndint(ns0)];
        if (c == a || deg[c] == 0) continue;
        int e = NB(c, rndint(deg[c]));
        if (AD(a, e) || AD(c, b)) continue;
        del_edge(a, b); del_edge(c, e);
        add_edge(a, e); add_edge(c, b);
        long nw = cost();
        if (nw <= cur || (nw == cur + 1 && rndint(10) == 0)) {
            cur = nw;
        } else {
            del_edge(a, e); del_edge(c, b);
            add_edge(a, b); add_edge(c, e);
        }
    }
    return cur;
}

static int *tu, *tv, *tc;
static int kill_flag[CAP], remap_buf[CAP];

/* Remove k random vertices from the current graph. */
static void kill_random(int k) {
    memset(kill_flag, 0, sizeof(int) * n);
    int cnt = 0;
    while (cnt < k) {
        int v = rndint(n);
        if (!kill_flag[v]) { kill_flag[v] = 1; cnt++; }
    }
    int nn = 0;
    for (int v = 0; v < n; v++) remap_buf[v] = kill_flag[v] ? -1 : nn++;
    int m = 0;
    for (int v = 0; v < n; v++) {
        if (kill_flag[v]) continue;
        for (int i = 0; i < deg[v]; i++) {
            int u = NB(v, i);
            if (v < u && !kill_flag[u]) {
                tu[m] = remap_buf[v]; tv[m] = remap_buf[u]; m++;
            }
        }
    }
    for (int v = 0; v < n; v++)
        if (!kill_flag[v]) tc[remap_buf[v]] = col[v];
    set_graph(nn, m, tu, tv, tc);
}

static int qbuf[CAP];

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    double t_end = now() + budget;
    if (d < 1 || d > 200 || D < 2 || D > 30) { printf("0 0\n"); return 0; }
    DEG = d; DIST = D;
    rs ^= (uint64_t)seed * 0xBF58476D1CE4E5B9ULL + 1;
    if (rs == 0) rs = 1;

    nb = malloc(sizeof(int) * (size_t)CAP * DEG);
    A = calloc((size_t)CAP * CAP, 1);
    ballA = calloc((size_t)CAP * WMAX, sizeof(uint64_t));
    ballB = calloc((size_t)CAP * WMAX, sizeof(uint64_t));
    tu = malloc(sizeof(int) * (size_t)CAP * DEG);
    tv = malloc(sizeof(int) * (size_t)CAP * DEG);
    tc = malloc(sizeof(int) * CAP);
    pa_buf = malloc(sizeof(int) * (size_t)CAP * CAP / 4 + 16);
    pb_buf = malloc(sizeof(int) * (size_t)CAP * CAP / 4 + 16);
    L_buf = malloc(sizeof(int) * CAP);
    R_buf = malloc(sizeof(int) * CAP);
    s0_buf = malloc(sizeof(int) * CAP);
    if (!nb || !A || !ballA || !ballB || !tu || !tv || !tc || !pa_buf || !pb_buf
        || !L_buf || !R_buf || !s0_buf) { printf("0 0\n"); return 0; }

    int N = 0, M = 0;
    if (scanf("%d %d", &N, &M) != 2 || N < 1 || N > CAP - 2 || M < 0) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(M + 1));
    int *ev = malloc(sizeof(int) * (size_t)(M + 1));
    int ok = 1;
    for (int i = 0; i < M; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { ok = 0; break; }
    }
    n = N;
    for (int i = 0; ok && i < M; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= N || v >= N || u == v || AD(u, v)
            || deg[u] >= DEG || deg[v] >= DEG) { ok = 0; break; }
        add_edge(u, v);
    }
    if (ok) {
        for (int v = 0; v < n; v++) col[v] = -1;
        for (int s = 0; s < n && ok; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int head = 0, tail = 0;
            qbuf[tail++] = s;
            while (head < tail && ok) {
                int u = qbuf[head++];
                for (int i = 0; i < deg[u]; i++) {
                    int w = NB(u, i);
                    if (col[w] < 0) { col[w] = 1 - col[u]; qbuf[tail++] = w; }
                    else if (col[w] == col[u]) { ok = 0; break; }
                }
            }
        }
    }
    if (ok && cost() != 0) ok = 0;
    if (!ok) { printf("0 0\n"); return 0; }

    Snap cur = snap_new();
    Snap best = snap_new();
    snap_take(&cur);
    snap_take(&best);
    int curN = n, bestN = n;

    static const int ks[6] = {1, 1, 2, 2, 3, 4};
    while (now() < t_end) {
        snap_load(&cur);
        if (n < 6) break;
        int k = ks[rndint(6)];
        kill_random(k);
        fill();
        if (anneal(150, t_end) != 0) continue;
        for (int rep = 0; rep < 60 && now() < t_end; rep++) {
            if (!try_grow()) break;
            fill();
        }
        if (cost() != 0) continue;
        if (n > bestN) { bestN = n; snap_take(&best); }
        if (n >= curN - 1) {
            snap_take(&cur);
            curN = n;
        } else if (n < bestN - 3) {
            snap_copy(&cur, &best);
            curN = bestN;
        }
    }

    printf("%d %d\n", best.n, best.m);
    for (int i = 0; i < best.m; i++) printf("%d %d\n", best.eu[i], best.ev[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _next_prime_power(d):
    q = max(2, d)
    while not lib.is_prime_power(q):
        q += 1
    return q


def _raw_big(d, D):
    """Dense structured graph of degree at least d, later thinned into a valid graph."""
    q = _next_prime_power(d)
    if D >= 4:
        if q > 16:
            return None
        return _gq_w(q)
    if q > 13:
        return None
    return lib.projective_plane_incidence(q)


# ----------------------------------------------------------------------------
# Shared Python helpers.
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
    """Two-colouring of a bipartite graph given by adjacency lists or sets."""
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
    """Greedy set cover of `full` by at most d candidate vertices. Returns list or None."""
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


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
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
            for attempt in range(200):
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
    """Greedily join deficient opposite-side vertices in random order. Keeps validity."""
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
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
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


# ----------------------------------------------------------------------------
# Twin duplication: a non-adjacent twin keeps distances and bipartiteness.
# ----------------------------------------------------------------------------

def _duplicate_twins(n, edges, d, rng):
    """Greedily add twins in random order while neighbours have spare degree."""
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


def _trial(base_n, base_e, d, D, rng, deadline):
    """One randomized pipeline: mix twin duplication with cover growth and saturation."""
    mode = rng.randrange(3)
    n, e = base_n, list(base_e)
    if mode == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    return n, e


# ----------------------------------------------------------------------------
# Thinning a dense structured graph into a valid one (degree reduction plus
# vertex deletion), then regrowing.
# ----------------------------------------------------------------------------

def _reduce_degree(n, edges, d, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    over = [v for v in range(n) if len(adj[v]) > d]
    while over:
        v = over.pop()
        while len(adj[v]) > d:
            u = max(adj[v], key=lambda x: (len(adj[x]), rng.random()))
            adj[v].discard(u)
            adj[u].discard(v)
            if len(adj[u]) > d:
                over.append(u)
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _delete_to_valid(n, edges, d, D, rng, deadline):
    """Delete the worst vertices in batches until the diameter bound holds. Returns (n, edges) or None."""
    adj = {v: set() for v in range(n)}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    while time.monotonic() < deadline:
        verts = sorted(adj)
        m = len(verts)
        if m == 0:
            return None
        idx = {v: i for i, v in enumerate(verts)}
        nbr = [[idx[u] for u in adj[v]] for v in verts]
        ball = _balls_radius(m, nbr, D)
        bad = [m - b.bit_count() for b in ball]
        if sum(bad) == 0:
            out = [(idx[v], idx[u]) for v in verts for u in adj[v] if v < u]
            return m, out
        order = sorted(range(m), key=lambda i: (-bad[i], rng.random()))
        k = max(1, m // 50)
        for i in order[:k]:
            v = verts[i]
            if v not in adj:
                continue
            for u in adj[v]:
                adj[u].discard(v)
            del adj[v]
    return None


def _deletion_trial(d, D, raw_n, raw_e, rng, deadline):
    """One thinning trial from the dense raw graph. Returns (n, edges) valid, or None."""
    e = _reduce_degree(raw_n, raw_e, d, rng)
    r = _delete_to_valid(raw_n, e, d, D, rng, deadline)
    if r is None:
        return None
    n2, e2 = r
    return _grow(n2, e2, d, D, deadline, rng)


# ----------------------------------------------------------------------------
# Driver.
#   A  structured base (W(q) or PG(2,q)) grown, twin-duplication trials
#   B  thinned dense graph (degree reduction + vertex deletion)
#   C  C engine: kill-repair-regrow LNS with bitset cost and switch annealing
# Every candidate passes lib.is_valid before it is kept; K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.88 * time_limit

    def at(f):
        return start + f * T

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Phase A: structured base, grown, then twin trials.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, at(0.05), rng)
            consider(n1, e1)
    if D >= 2:
        trial_end = at(0.12)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase B: thinned dense graph.
    if D >= 2 and time.monotonic() < at(0.22):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.22):
                r = _deletion_trial(d, D, rn, re, rng, at(0.22))
                if r is None:
                    break
                consider(*r)

    # Phase C: C engine LNS from the best valid graph found so far.
    if D >= 2 and best_n <= 3000:
        remaining = at(1.0) - time.monotonic() - 1.0
        if remaining > 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed % 1000003 + 1, round(remaining, 2)],
                                stdin_graph=(best_n, best_e), timeout=remaining + 10.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
