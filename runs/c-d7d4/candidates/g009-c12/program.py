import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Structured starting graphs (Python constructions).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C search engine.
#
# Bitset-based annealing over bipartite graphs with max degree d and diameter D.
# State is always valid (cost 0). Moves:
#   - cover growth: add a vertex whose neighbours' (D-1)-balls cover the graph;
#   - repair growth: add a vertex (stealing edges if needed), fill spare degree,
#     then anneal with degree-preserving bipartite double-edge switches;
#   - kill-regrow: delete 1-3 vertices, repair with annealing, regrow.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXW ((MAXN + 63) / 64)
#define DMAX 40
#define ITER_REP 1500
#define ITER_LNS 3000
#define T_HOT 1.5
#define T_COLD 0.15

typedef struct {
    int n;
    int deg[MAXN];
    int side[MAXN];
    int adj[MAXN][DMAX];
    uint64_t bits[MAXN][MAXW];
} Graph;

static int dd = 0, DD = 0;
static double DEADLINE = 0.0;
static uint64_t rs = 88172645463325252ULL;
static uint64_t BALL[MAXN][MAXW];
static uint64_t TA[MAXN][MAXW], TB[MAXN][MAXW];
static Graph CUR, BEST, SAVE1, SAVE2, SAVE3, TMP, INPUT;

static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(const Graph *g, int a, int b) {
    return (int)((g->bits[a][b >> 6] >> (b & 63)) & 1ULL);
}

static void add_edge(Graph *g, int a, int b) {
    g->adj[a][g->deg[a]++] = b;
    g->adj[b][g->deg[b]++] = a;
    g->bits[a][b >> 6] |= 1ULL << (b & 63);
    g->bits[b][a >> 6] |= 1ULL << (a & 63);
}

static void del_dir(Graph *g, int a, int b) {
    int k;
    for (k = 0; k < g->deg[a]; k++) {
        if (g->adj[a][k] == b) {
            g->adj[a][k] = g->adj[a][--g->deg[a]];
            break;
        }
    }
    g->bits[a][b >> 6] &= ~(1ULL << (b & 63));
}

static void remove_edge(Graph *g, int a, int b) {
    del_dir(g, a, b);
    del_dir(g, b, a);
}

/* BALL[v] = bitmask of vertices within distance r of v. */
static void balls(const Graph *g, int r) {
    int n = g->n, W = (n + 63) / 64, v, i, k, t;
    uint64_t (*cur)[MAXW] = TA;
    uint64_t (*nxt)[MAXW] = TB;
    uint64_t (*tmp)[MAXW];
    for (v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * W);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (t = 0; t < r; t++) {
        for (v = 0; v < n; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * W);
            for (k = 0; k < g->deg[v]; k++) {
                const uint64_t *src = cur[g->adj[v][k]];
                for (i = 0; i < W; i++) nxt[v][i] |= src[i];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    for (v = 0; v < n; v++) memcpy(BALL[v], cur[v], sizeof(uint64_t) * W);
}

/* Number of unordered pairs at distance > DD (unreachable counts). */
static int cost_of(const Graph *g) {
    int n = g->n, W = (n + 63) / 64, v, i;
    long long bad = 0;
    balls(g, DD);
    for (v = 0; v < n; v++) {
        int c = 0;
        for (i = 0; i < W; i++) c += pc(BALL[v][i]);
        bad += n - c;
    }
    return (int)(bad / 2);
}

static void shuffle_int(int *a, int m) {
    int i;
    for (i = m - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Add cross-side edges between deficient vertices (never increases cost). */
static void fill(Graph *g) {
    static int L[MAXN], R[MAXN];
    int n = g->n, i, j, nl = 0, nr = 0;
    for (i = 0; i < n; i++) {
        if (g->deg[i] < dd) {
            if (g->side[i] == 0) L[nl++] = i;
            else R[nr++] = i;
        }
    }
    shuffle_int(L, nl);
    shuffle_int(R, nr);
    for (i = 0; i < nl; i++) {
        int a = L[i];
        for (j = 0; j < nr && g->deg[a] < dd; j++) {
            int b = R[j];
            if (g->deg[b] < dd && !has_edge(g, a, b)) add_edge(g, a, b);
        }
    }
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs. */
static int anneal(Graph *g, long iters, double T0, double T1) {
    static int S0[MAXN];
    int n = g->n, cur, v, m0 = 0;
    long it;
    cur = cost_of(g);
    if (cur == 0) return 1;
    for (v = 0; v < n; v++)
        if (g->side[v] == 0 && g->deg[v] > 0) S0[m0++] = v;
    if (m0 < 2) return 0;
    for (it = 0; it < iters && cur > 0; it++) {
        double T;
        int a, b, c, e, nw;
        if ((it & 31) == 0 && now() > DEADLINE) break;
        T = T0 + (T1 - T0) * ((double)it / (double)iters);
        a = S0[rndint(m0)];
        c = S0[rndint(m0)];
        if (a == c || g->deg[a] == 0 || g->deg[c] == 0) continue;
        b = g->adj[a][rndint(g->deg[a])];
        e = g->adj[c][rndint(g->deg[c])];
        if (has_edge(g, a, e) || has_edge(g, c, b)) continue;
        remove_edge(g, a, b);
        remove_edge(g, c, e);
        add_edge(g, a, e);
        add_edge(g, c, b);
        nw = cost_of(g);
        if (nw <= cur || rnd01() < exp(-(double)(nw - cur) / T)) {
            cur = nw;
        } else {
            remove_edge(g, a, e);
            remove_edge(g, c, b);
            add_edge(g, a, b);
            add_edge(g, c, e);
        }
    }
    return cur == 0;
}

/* Append a vertex on a random side, joined to dd opposite-side vertices (stealing if full). */
static void repair_add(Graph *g) {
    static int cand[MAXN];
    int n = g->n, v = n, sv = rndint(2), opp = 1 - sv, k;
    g->n = n + 1;
    g->side[v] = sv;
    g->deg[v] = 0;
    memset(g->bits[v], 0, sizeof(g->bits[v]));
    for (k = 0; k < dd; k++) {
        int nc = 0, u, t;
        for (u = 0; u < n; u++)
            if (g->side[u] == opp && g->deg[u] < dd && !has_edge(g, v, u)) cand[nc++] = u;
        if (nc > 0) {
            add_edge(g, v, cand[rndint(nc)]);
            continue;
        }
        nc = 0;
        for (u = 0; u < n; u++)
            if (g->side[u] == opp && !has_edge(g, v, u)) cand[nc++] = u;
        if (nc == 0) break;
        u = cand[rndint(nc)];
        if (g->deg[u] == 0) {
            add_edge(g, v, u);
            continue;
        }
        t = g->adj[u][rndint(g->deg[u])];
        remove_edge(g, u, t);
        add_edge(g, v, u);
    }
}

/* Add one vertex whose neighbours' (D-1)-balls cover all vertices. Keeps cost 0. */
static int cover_add(Graph *g, int attempts) {
    static int chosen[DMAX];
    int n = g->n, W = (n + 63) / 64, at, i, c;
    uint64_t full[MAXW], unc[MAXW];
    if (n >= MAXN - 1 || DD < 2) return 0;
    balls(g, DD - 1);
    memset(full, 0, sizeof(full));
    for (i = 0; i < n; i++) full[i >> 6] |= 1ULL << (i & 63);
    for (at = 0; at < attempts; at++) {
        int nch = 0, ok = 0;
        c = rndint(2);
        memcpy(unc, full, sizeof(uint64_t) * W);
        while (nch < dd) {
            int best = -1, u;
            long bestsc = 0;
            for (u = 0; u < n; u++) {
                int gain = 0;
                long sc;
                if (g->side[u] != c || g->deg[u] >= dd) continue;
                for (i = 0; i < W; i++) gain += pc(BALL[u][i] & unc[i]);
                if (gain == 0) continue;
                sc = (long)gain * 4096 + (at == 0 ? 0 : rndint(4096));
                if (sc > bestsc) {
                    bestsc = sc;
                    best = u;
                }
            }
            if (best < 0) break;
            chosen[nch++] = best;
            for (i = 0; i < W; i++) unc[i] &= ~BALL[best][i];
            ok = 1;
            for (i = 0; i < W; i++)
                if (unc[i]) { ok = 0; break; }
            if (ok) break;
        }
        if (ok) {
            int v = n, j;
            g->n = n + 1;
            g->side[v] = 1 - c;
            g->deg[v] = 0;
            memset(g->bits[v], 0, sizeof(g->bits[v]));
            for (j = 0; j < nch; j++) add_edge(g, chosen[j], v);
            return 1;
        }
    }
    return 0;
}

static int repair_try(Graph *g, Graph *save, long iters) {
    if (g->n >= MAXN - 2) return 0;
    *save = *g;
    repair_add(g);
    fill(g);
    if (anneal(g, iters, T_HOT, T_COLD)) return 1;
    *g = *save;
    return 0;
}

/* Build dst = src minus the vertices marked in dead. */
static void kill_into(const Graph *src, Graph *dst, const int *dead) {
    static int map[MAXN];
    int n = src->n, v, k, m = 0;
    memset(dst->deg, 0, sizeof(dst->deg));
    memset(dst->bits, 0, sizeof(dst->bits));
    for (v = 0; v < n; v++) map[v] = dead[v] ? -1 : m++;
    dst->n = m;
    for (v = 0; v < n; v++) {
        if (map[v] < 0) continue;
        dst->side[map[v]] = src->side[v];
        for (k = 0; k < src->deg[v]; k++) {
            int u = src->adj[v][k];
            if (map[u] >= 0 && v < u) add_edge(dst, map[v], map[u]);
        }
    }
}

static void lns_step(void) {
    static int dead[MAXN];
    int n = CUR.n, k = 1 + rndint(3), cnt = 0, t;
    memset(dead, 0, sizeof(dead));
    while (cnt < k) {
        int v = rndint(n);
        if (!dead[v]) {
            dead[v] = 1;
            cnt++;
        }
    }
    SAVE2 = CUR;
    kill_into(&CUR, &TMP, dead);
    CUR = TMP;
    fill(&CUR);
    if (!anneal(&CUR, ITER_LNS, T_HOT, T_COLD)) {
        CUR = SAVE2;
        return;
    }
    for (t = 0; t < 6 && now() < DEADLINE; t++) {
        while (cover_add(&CUR, 8)) fill(&CUR);
        if (CUR.n >= SAVE2.n) break;
        repair_try(&CUR, &SAVE3, ITER_REP);
    }
    if (CUR.n < SAVE2.n - 1) CUR = SAVE2;
}

static long moore_c(void) {
    long s = 0, p = 1;
    int i;
    if (dd < 2 || DD < 1) return 2;
    for (i = 0; i < DD; i++) {
        s += p;
        p *= (dd - 1);
        if (p > 1000000) p = 1000000;
    }
    return 2 * s;
}

static int bipartition(Graph *g) {
    static int q[MAXN];
    int col[MAXN];
    int s, v, k, h, t;
    for (v = 0; v < g->n; v++) col[v] = -1;
    for (s = 0; s < g->n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        h = 0;
        t = 0;
        q[t++] = s;
        while (h < t) {
            v = q[h++];
            for (k = 0; k < g->deg[v]; k++) {
                int w = g->adj[v][k];
                if (col[w] < 0) {
                    col[w] = 1 - col[v];
                    q[t++] = w;
                } else if (col[w] == col[v]) {
                    return 0;
                }
            }
        }
    }
    for (v = 0; v < g->n; v++) g->side[v] = col[v];
    return 1;
}

static int read_graph(Graph *g) {
    int n, m, i;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 1 || n > MAXN - 2 || m < 0) return 0;
    memset(g, 0, sizeof(*g));
    g->n = n;
    for (i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (has_edge(g, u, v) || g->deg[u] >= DMAX || g->deg[v] >= DMAX) continue;
        add_edge(g, u, v);
    }
    return bipartition(g);
}

static int max_deg(const Graph *g) {
    int v, m = 0;
    for (v = 0; v < g->n; v++)
        if (g->deg[v] > m) m = g->deg[v];
    return m;
}

static void print_graph(const Graph *g) {
    int v, k, m = 0;
    for (v = 0; v < g->n; v++)
        for (k = 0; k < g->deg[v]; k++)
            if (g->adj[v][k] > v) m++;
    printf("%d %d\n", g->n, m);
    for (v = 0; v < g->n; v++)
        for (k = 0; k < g->deg[v]; k++)
            if (g->adj[v][k] > v) printf("%d %d\n", v, g->adj[v][k]);
}

int main(int argc, char **argv) {
    unsigned long long seed;
    double budget;
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    seed = strtoull(argv[3], NULL, 10);
    budget = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    DEADLINE = now() + budget;

    if (!read_graph(&INPUT)) {
        printf("0 0\n");
        return 0;
    }
    if (dd < 1 || dd > DMAX || DD < 2 || max_deg(&INPUT) > dd) {
        print_graph(&INPUT);
        return 0;
    }
    CUR = INPUT;
    if (cost_of(&CUR) != 0 && !anneal(&CUR, 20000, T_HOT, T_COLD)) {
        print_graph(&INPUT);
        return 0;
    }
    BEST = CUR;

    while (now() < DEADLINE && BEST.n < moore_c()) {
        while (cover_add(&CUR, 6)) fill(&CUR);
        if (rndint(10) < 6) repair_try(&CUR, &SAVE1, ITER_REP);
        else lns_step();
        if (CUR.n > BEST.n) BEST = CUR;
        if (CUR.n + 3 < BEST.n) CUR = BEST;
    }

    if (cost_of(&BEST) == 0) print_graph(&BEST);
    else print_graph(&INPUT);
    return 0;
}
"""


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if D >= 4:
        base = _best_gq(d)
        if base is not None:
            consider(*base)
    if D == 3:
        base = _best_pg(d)
        if base is not None:
            consider(*base)
        if d >= 5 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except ValueError:
                pass

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    elapsed = time.monotonic() - t0
    remaining = 0.9 * time_limit - elapsed
    budget = min(0.75 * time_limit - elapsed, remaining - 1.5)
    if budget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=(best_n, list(best_e)), timeout=remaining)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
