"""Bold variant: fresh random-regular anneals at target size, plus pair-insertion anneals from the best graph.

Starts from the best algebraic graph (hexagon / W(q) / projective plane / Araujo-Lopez). The C engine
alternates two moves. A fresh move builds a random d-regular bipartite graph one step above the current
best order and anneals it with degree-preserving 2-switches on a sampled objective. A grow move inserts
one vertex pair into the best graph and anneals the same way. Exact all-pairs checks decide acceptance,
and the best valid graph is always printed, so the output stays valid.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)
#define NSRC 40

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static Graph best, work;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void del_half(Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
}

static void del_edge(Graph *g, int u, int v) {
    del_half(g, u, v);
    del_half(g, v, u);
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Exact number of unordered pairs at distance > D; sets badv[v] = unreached count from v. */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        badv[v] = n - c;
        total += n - c;
    }
    return total / 2;
}

static int structure_ok(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return 1;
}

static int is_valid(const Graph *g) {
    return structure_ok(g) && bad_pairs(g) == 0;
}

/* Number of vertices within distance D of src (src included). */
static int ball_mark[MAXN], bq[MAXN];
static int ball_stamp = 0;

static int ball_count(const Graph *g, int src) {
    int head = 0, tail = 0;
    if (++ball_stamp == 0x7fffffff) {
        memset(ball_mark, 0, sizeof ball_mark);
        ball_stamp = 1;
    }
    ball_mark[src] = ball_stamp;
    bq[tail++] = src;
    for (int lev = 0; lev < D && head < tail; lev++) {
        int end = tail;
        while (head < end) {
            int v = bq[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (ball_mark[u] != ball_stamp) {
                    ball_mark[u] = ball_stamp;
                    bq[tail++] = u;
                }
            }
        }
    }
    return tail;
}

static void read_start(Graph *g) {
    static int q[MAXN];
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD || has_edge(g, u, v)) {
            g->n = 0;
            return;
        }
        add_edge(g, u, v);
    }
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        q[tail++] = s;
        while (head < tail) {
            int v = q[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; q[tail++] = u; }
                else if (g->side[u] == g->side[v]) { g->n = 0; return; }
            }
        }
    }
    if (!is_valid(g)) g->n = 0;
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* Configuration-style random d-regular simple bipartite graph on N vertices (sides [0,M) and [M,N)). */
static int random_regular(Graph *g, int N) {
    if (N < 2 * d || (N & 1)) return 0;
    int M = N / 2;
    for (int attempt = 0; attempt < 200; attempt++) {
        g->n = N;
        for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = v >= M; }
        int ok = 1;
        for (int a = 0; a < M && ok; a++) {
            for (int k = 0; k < d && ok; k++) {
                int off = rndint(M), placed = 0;
                for (int t = 0; t < M; t++) {
                    int b = M + (off + t) % M;
                    if (g->deg[b] < d && !has_edge(g, a, b)) {
                        add_edge(g, a, b);
                        placed = 1;
                        break;
                    }
                }
                if (!placed) ok = 0;
            }
        }
        if (ok) return 1;
    }
    return 0;
}

/* Insert one vertex pair x (side 0), y (side 1) into base by stealing d-1 edges. Degrees stay exact. */
static int grow_pair(const Graph *base, Graph *w) {
    int n = base->n;
    if (n + 2 > MAXN) return 0;
    copy_graph(w, base);
    int x = n, y = n + 1;
    w->n = n + 2;
    w->deg[x] = w->deg[y] = 0;
    w->side[x] = 0;
    w->side[y] = 1;
    add_edge(w, x, y);
    int got = 0;
    for (int tries = 0; got < d - 1 && tries < 200000; tries++) {
        int a = rndint(n);
        if (base->side[a] != 0 || w->deg[a] == 0) continue;
        int b = w->adj[a][rndint(w->deg[a])];
        if (b >= n) continue;
        if (has_edge(w, x, b) || has_edge(w, y, a)) continue;
        del_edge(w, a, b);
        add_edge(w, x, b);
        add_edge(w, y, a);
        got++;
    }
    return got == d - 1;
}

static int S_src[NSRC];

static int pick_bad(int n) {
    for (int t = 0; t < 50; t++) {
        int v = rndint(n);
        if (badv[v] > 0) return v;
    }
    int off = rndint(n);
    for (int t = 0; t < n; t++) {
        int v = (off + t) % n;
        if (badv[v] > 0) return v;
    }
    return rndint(n);
}

/* Sampled objective: sum over sources of vertices unreached within D. */
static long sample_F(const Graph *g) {
    long f = 0;
    for (int i = 0; i < NSRC; i++) f += g->n - ball_count(g, S_src[i]);
    return f;
}

/* Degree-preserving 2-switch annealing on the sampled objective. Returns 1 once g is valid. */
static int anneal(Graph *g, double until) {
    int n = g->n;
    for (int i = 0; i < NSRC; i++) S_src[i] = rndint(n);
    long f = sample_F(g), bestf = f, since = 0, iter = 0;
    double T = 1.0;
    for (;;) {
        if (f == 0) {
            if (bad_pairs(g) == 0) return 1;
            for (int i = 0; i < NSRC / 2; i++) S_src[i] = pick_bad(n);
            f = sample_F(g);
            bestf = f;
            since = 0;
            continue;
        }
        if ((++iter & 31) == 0 && now() > until) return 0;
        if (iter % 4000 == 0) {
            S_src[rndint(NSRC)] = rndint(n);
            f = sample_F(g);
            bestf = f;
            since = 0;
            continue;
        }
        int a = rndint(n), c = rndint(n);
        if (g->side[a] != 0 || g->side[c] != 0 || a == c || g->deg[a] == 0 || g->deg[c] == 0)
            continue;
        int u = g->adj[a][rndint(g->deg[a])];
        int t = g->adj[c][rndint(g->deg[c])];
        if (u == t || has_edge(g, a, t) || has_edge(g, c, u)) continue;
        del_edge(g, a, u);
        del_edge(g, c, t);
        add_edge(g, a, t);
        add_edge(g, c, u);
        long nf = sample_F(g);
        if (nf <= f || rnd01() < exp((double)(f - nf) / T)) {
            f = nf;
        } else {
            del_edge(g, a, t);
            del_edge(g, c, u);
            add_edge(g, a, u);
            add_edge(g, c, t);
        }
        if (f < bestf) { bestf = f; since = 0; }
        else since++;
        if (since > 30000) { T = 1.0; since = 0; bestf = f; }
        T *= 0.9997;
        if (T < 0.1) T = 0.1;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    long moore = moore_bound();
    while (now() < t_end && best.n + 2 <= moore && best.n + 2 <= MAXN) {
        double left = t_end - now();
        if (left < 0.5) break;
        int ok = 0;
        if (rndint(3) == 0) {
            int N = best.n + 2;
            if (N & 1) N++;
            if (N > moore || N > MAXN) continue;
            if (!random_regular(&work, N)) continue;
            ok = anneal(&work, now() + left * 0.2);
        } else {
            if (!grow_pair(&best, &work)) continue;
            ok = anneal(&work, now() + left * 0.25);
        }
        if (ok && work.n > best.n && is_valid(&work)) copy_graph(&best, &work);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    Characteristic 2, so signs are irrelevant. The caller validates the result with lib.is_valid.
    """
    F = lib.GF(q)
    MT, AT = F.mul_table, F.add_table
    pts = []
    for v in itertools.product(range(q), repeat=7):
        if any(v) and next(c for c in v if c) == 1:
            s = AT[AT[MT[v[0], v[4]], MT[v[1], v[5]]], AT[MT[v[2], v[6]], MT[v[3], v[3]]]]
            if s == 0:
                pts.append(tuple(int(c) for c in v))
    N = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    P = np.array(pts, dtype=np.int64)
    lines = set()
    for i in range(N - 1):
        x = P[i]
        Y = P[i + 1:]

        def pp(a, b):
            """Grassmann coordinate p_ab = x_a y_b - x_b y_a, for all y in Y."""
            return AT[MT[x[a], Y[:, b]], MT[x[b], Y[:, a]]]

        s = np.zeros(len(Y), dtype=np.int64)
        for a, b in ((0, 4), (1, 5), (2, 6)):
            s = AT[s, AT[MT[x[a], Y[:, b]], MT[Y[:, a], x[b]]]]
        ok = (s == 0)
        ok &= pp(1, 2) == pp(3, 4)
        ok &= pp(5, 4) == pp(3, 2)
        ok &= pp(2, 0) == pp(3, 5)
        ok &= pp(6, 5) == pp(3, 0)
        ok &= pp(0, 1) == pp(3, 6)
        ok &= pp(4, 6) == pp(3, 1)
        for jj in np.nonzero(ok)[0]:
            y = Y[jj]
            vecs = [tuple(int(c) for c in x)]
            for t in range(q):
                vecs.append(tuple(int(AT[MT[t, x[k]], y[k]]) for k in range(7)))
            idx = []
            for v in vecs:
                c = next(e for e in v if e)
                inv = F.inv(c)
                idx.append(index[tuple(F.mul(inv, e) for e in v)])
            lines.add(tuple(sorted(idx)))
    lines = sorted(lines)
    edges = [(pt, N + k) for k, L in enumerate(lines) for pt in L]
    return 2 * N, edges


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates (may be empty); build() keeps only those that pass lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 6 and d - 1 in (2, 4):
        try:
            out.append(_hexagon_incidence(d - 1))
        except Exception:
            pass
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            try:
                out.append(_gq_w(q))
            except Exception:
                pass
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
