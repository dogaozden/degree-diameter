import itertools
import time

import lib


C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXD 24
#define MAXW (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int col[MAXN];
    int adj[MAXN][MAXD];
} State;

static State G, CUR, BEST, SNAP, TMPS;
static int d_, D_;
static uint64_t rng_s = 88172645463325252ULL;
static uint64_t BD[MAXN][MAXW];
static uint64_t BD1[MAXN][MAXW];
static uint64_t TB[2][MAXN][MAXW];

static uint64_t rnd64(void) {
    rng_s ^= rng_s << 13;
    rng_s ^= rng_s >> 7;
    rng_s ^= rng_s << 17;
    return rng_s;
}
static unsigned rnd(unsigned m) { return (unsigned)(rnd64() % (uint64_t)m); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int has_edge(const State *s, int u, int v) {
    for (int i = 0; i < s->deg[u]; i++) if (s->adj[u][i] == v) return 1;
    return 0;
}
static void rem1(State *s, int u, int v) {
    for (int i = 0; i < s->deg[u]; i++) {
        if (s->adj[u][i] == v) { s->adj[u][i] = s->adj[u][--s->deg[u]]; return; }
    }
}
static void repl(State *s, int u, int old, int nw) {
    for (int i = 0; i < s->deg[u]; i++) {
        if (s->adj[u][i] == old) { s->adj[u][i] = nw; return; }
    }
}
static void add_e(State *s, int u, int v) {
    s->adj[u][s->deg[u]++] = v;
    s->adj[v][s->deg[v]++] = u;
}
static void del_e(State *s, int u, int v) { rem1(s, u, v); rem1(s, v, u); }

/* remove a-b, c-e; add a-e, c-b (a,c on one side; b,e on the other). Degrees kept. */
static void do_switch(State *s, int a, int b, int c, int e) {
    repl(s, a, b, e);
    repl(s, b, a, c);
    repl(s, c, e, b);
    repl(s, e, c, a);
}

/* ball[v] = bitset of vertices within distance r of v. */
static void balls(const State *s, int r, uint64_t out[][MAXW]) {
    int n = s->n;
    int W = (n + 63) >> 6;
    int c = 0;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) TB[0][v][w] = 0;
        TB[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int step = 0; step < r; step++) {
        int a = c, b = 1 - c;
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) TB[b][v][w] = TB[a][v][w];
            for (int i = 0; i < s->deg[v]; i++) {
                int u = s->adj[v][i];
                for (int w = 0; w < W; w++) TB[b][v][w] |= TB[a][u][w];
            }
        }
        c = b;
    }
    for (int v = 0; v < n; v++)
        for (int w = 0; w < W; w++) out[v][w] = TB[c][v][w];
}

/* Number of unordered pairs at distance greater than D_ (unreachable counts). */
static long long cost(const State *s) {
    balls(s, D_, BD);
    int n = s->n, W = (n + 63) >> 6;
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(BD[v][w]);
        tot += n - c;
    }
    return tot / 2;
}

static int pick_side0(void) {
    int n = G.n;
    for (int t = 0; t < 400; t++) {
        int v = (int)rnd((unsigned)n);
        if (G.col[v] == 0 && G.deg[v] > 0) return v;
    }
    return -1;
}

static void shuffle_int(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = (int)rnd((unsigned)(i + 1));
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* Join deficient opposite-side non-adjacent pairs (only shortens distances). */
static void fill(State *s) {
    static int L[MAXN], R[MAXN];
    int n = s->n, nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (s->deg[v] < d_) {
            if (s->col[v] == 0) L[nl++] = v; else R[nr++] = v;
        }
    }
    shuffle_int(L, nl);
    shuffle_int(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr; j++) {
            if (s->deg[a] >= d_) break;
            int b = R[j];
            if (s->deg[b] < d_ && !has_edge(s, a, b)) add_e(s, a, b);
        }
    }
}

/* Metropolis anneal with degree-preserving bipartite switches on G. True if cost reaches 0. */
static int anneal(int iters, double end) {
    long long c = cost(&G);
    for (int it = 0; it < iters && c > 0; it++) {
        if (now() > end) break;
        int a = pick_side0();
        if (a < 0) break;
        int cc = pick_side0();
        if (cc < 0 || cc == a) continue;
        int b = G.adj[a][rnd((unsigned)G.deg[a])];
        int e = G.adj[cc][rnd((unsigned)G.deg[cc])];
        if (b == e) continue;
        if (has_edge(&G, a, e) || has_edge(&G, cc, b)) continue;
        do_switch(&G, a, b, cc, e);
        long long nc = cost(&G);
        if (nc <= c || rndu() < exp(-(double)(nc - c) / 0.4)) {
            c = nc;
        } else {
            do_switch(&G, a, e, cc, b);
        }
    }
    return c == 0;
}

/* Add twins (same neighbourhood) of vertices whose neighbours have spare degree.
   Twins keep all distances, so the diameter stays valid. Returns number added. */
static int twin_pass(void) {
    static int ord[MAXN];
    int n = G.n, added = 0;
    for (int v = 0; v < n; v++) ord[v] = v;
    shuffle_int(ord, n);
    for (int k = 0; k < n; k++) {
        if (G.n >= MAXN - 2) break;
        int v = ord[k];
        if (G.deg[v] == 0) continue;
        int ok = 1;
        for (int i = 0; i < G.deg[v]; i++) {
            if (G.deg[G.adj[v][i]] >= d_) { ok = 0; break; }
        }
        if (!ok) continue;
        int w = G.n++;
        G.col[w] = 1 - G.col[v];
        G.deg[w] = 0;
        for (int i = 0; i < G.deg[v]; i++) {
            int u = G.adj[v][i];
            add_e(&G, u, w);
        }
        added++;
    }
    return added;
}

/* Add one vertex joined to a greedy cover of the opposite side, then repair by annealing.
   On failure G is restored. Returns 1 on success. */
static int cover_grow(int iters, double end) {
    int n = G.n;
    if (n + 2 >= MAXN) return 0;
    int W = (n + 63) >> 6;
    SNAP = G;
    balls(&G, D_ - 1, BD1);
    int s = (int)rnd(2);
    uint64_t cov[MAXW];
    for (int w = 0; w < W; w++) cov[w] = 0;
    static int used[MAXN];
    for (int x = 0; x < n; x++) used[x] = 0;
    int chosen[MAXD];
    int nc = 0;
    for (int k = 0; k < d_; k++) {
        int bx = -1;
        long long bs = -1;
        for (int x = 0; x < n; x++) {
            if (G.col[x] != s || used[x]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += __builtin_popcountll(BD1[x][w] & ~cov[w]);
            if (g == 0) continue;
            long long sc = 4LL * g + (G.deg[x] < d_ ? 2 : 0) + (long long)rnd(3);
            if (sc > bs) { bs = sc; bx = x; }
        }
        if (bx < 0) break;
        used[bx] = 1;
        chosen[nc++] = bx;
        for (int w = 0; w < W; w++) cov[w] |= BD1[bx][w];
    }
    if (nc == 0) return 0;
    int v = G.n++;
    G.col[v] = 1 - s;
    G.deg[v] = 0;
    for (int k = 0; k < nc; k++) {
        int x = chosen[k];
        if (G.deg[x] >= d_) {
            int y = G.adj[x][rnd((unsigned)G.deg[x])];
            del_e(&G, x, y);
        }
        add_e(&G, x, v);
    }
    fill(&G);
    if (anneal(iters, end)) return 1;
    G = SNAP;
    return 0;
}

static void accept(void) {
    CUR = G;
    if (G.n > BEST.n) BEST = G;
}

static void grow_attempt(double end) {
    G = CUR;
    if (rnd(4) == 0) {
        int t = twin_pass();
        if (t > 0 && cost(&G) == 0) { accept(); return; }
        G = CUR;
    }
    if (cover_grow(1200, end)) accept();
}

/* Kill k random vertices, repair by fill+anneal, regrow a few vertices. */
static void lns_step(double end) {
    static int kill[MAXN], mp[MAXN];
    int n = CUR.n;
    int k = 1 + (int)rnd(3);
    if (n < k + 6) return;
    for (int v = 0; v < n; v++) kill[v] = 0;
    for (int i = 0; i < k; i++) {
        int x;
        do { x = (int)rnd((unsigned)n); } while (kill[x]);
        kill[x] = 1;
    }
    int m = 0;
    for (int v = 0; v < n; v++) mp[v] = kill[v] ? -1 : m++;
    TMPS.n = m;
    for (int v = 0; v < n; v++) {
        if (mp[v] < 0) continue;
        int nv = mp[v];
        TMPS.col[nv] = CUR.col[v];
        TMPS.deg[nv] = 0;
        for (int i = 0; i < CUR.deg[v]; i++) {
            int u = CUR.adj[v][i];
            if (mp[u] >= 0) TMPS.adj[nv][TMPS.deg[nv]++] = mp[u];
        }
    }
    G = TMPS;
    fill(&G);
    if (!anneal(800, end)) return;
    for (int r = 0; r < 6; r++) {
        if (!cover_grow(800, end)) break;
    }
    if (G.n >= CUR.n - 1) accept();
}

static int read_graph(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN - 64 || m < 0) return 0;
    G.n = n;
    for (int v = 0; v < n; v++) G.deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (G.deg[u] >= d_ || G.deg[v] >= d_ || has_edge(&G, u, v)) return 0;
        add_e(&G, u, v);
    }
    static int stk[MAXN];
    for (int v = 0; v < n; v++) G.col[v] = -1;
    for (int s0 = 0; s0 < n; s0++) {
        if (G.col[s0] != -1) continue;
        int sp = 0;
        G.col[s0] = 0;
        stk[sp++] = s0;
        while (sp > 0) {
            int x = stk[--sp];
            for (int i = 0; i < G.deg[x]; i++) {
                int y = G.adj[x][i];
                if (G.col[y] == -1) {
                    G.col[y] = 1 - G.col[x];
                    stk[sp++] = y;
                } else if (G.col[y] == G.col[x]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void make_kdd(void) {
    G.n = 2 * d_;
    for (int v = 0; v < G.n; v++) {
        G.deg[v] = 0;
        G.col[v] = (v < d_) ? 0 : 1;
    }
    for (int i = 0; i < d_; i++)
        for (int j = 0; j < d_; j++)
            add_e(&G, i, d_ + j);
}

static void output(const State *s) {
    long long sum = 0;
    for (int v = 0; v < s->n; v++) sum += s->deg[v];
    printf("%d %lld\n", s->n, sum / 2);
    for (int v = 0; v < s->n; v++)
        for (int i = 0; i < s->deg[v]; i++) {
            int u = s->adj[v][i];
            if (v < u) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rng_s = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rng_s == 0) rng_s = 1;
    if (d_ < 1 || d_ > MAXD || D_ < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    double end = t0 + tl;
    if (!read_graph()) make_kdd();
    if (cost(&G) != 0) {
        if (!anneal(20000, t0 + 0.2 * tl)) make_kdd();
    }
    CUR = G;
    BEST = G;
    while (now() < end) {
        if (CUR.n < BEST.n - 3) CUR = BEST;
        if (rnd(10) < 7) grow_attempt(end);
        else lns_step(end);
    }
    output(&BEST);
    return 0;
}
'''


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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (small q only)."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2
    if best[0] >= lib.moore_bound(d, D):
        return best

    # Structured base: W(q) for D >= 4, PG(2, q) for D = 3.
    base = None
    try:
        if D >= 4:
            base = _best_gq(d)
        if base is None and D >= 3:
            base = _best_pg(d)
    except Exception:
        base = None
    if base is not None and base[0] <= 3000 and base[0] > best[0]:
        if lib.is_valid(base[0], base[1], d, D):
            best = (base[0], list(base[1]))

    if best[0] >= lib.moore_bound(d, D):
        return best

    # One C run: grow and repair from the best valid start.
    elapsed = time.monotonic() - t0
    budget = 0.75 * time_limit - elapsed
    if budget > 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best,
                            timeout=max(1.0, 0.9 * time_limit - elapsed))
            n, e = lib.parse_graph_text(out)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, list(e))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
