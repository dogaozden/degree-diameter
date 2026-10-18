"""Bi-Cayley lifts over non-metacyclic matrix groups, searched in ascending order of size.

The parent searched metacyclic groups. This version searches lifts of small base multigraphs
(p fibres per side, d-regular) over the groups SL(2,q), PSL(2,q) and PGL(2,q) for prime q.
These groups are not metacyclic. The record 2184 equals 2*|PSL(2,13)|, so this family contains
the record structure for d=4, D=8.

C side: enumerate every (group, p) configuration with order 2pN in (best, Moore]. Pick the
configuration with the fewest failed slices, breaking ties by smallest order. Anneal the voltages
against an exact orbit-reduced diameter count (BFS from the 2p fibre identities), and validate
any success with the full bitset check. Each success raises the current best, and configurations
below it are dropped. Python builds the algebraic starts and only accepts a C result if it is
valid and strictly larger.
"""
import time

import itertools

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXP 12
#define MAXDART (MAXD * MAXP)
#define MAXQ 17
#define MAXCFG 512

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int type, q, p, N, T; } Cfg;

static int d, D;
static long MOORE;
static double t_end;

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

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

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

/* Number of unordered pairs at distance > D (bitset ball expansion). */
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

static int is_valid(const Graph *g) {
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
    return bad_pairs(g) == 0;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; queue[tail++] = u; }
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

/* ---- matrix groups over GF(q), q prime: type 0 = SL(2,q), 1 = PSL(2,q), 2 = PGL(2,q). ---- */

static int gm_type = -1, gm_q = 0, gm_N = 0;
static int EA[MAXN], EB[MAXN], EC[MAXN], EE[MAXN];
static int IDX[MAXQ * MAXQ * MAXQ * MAXQ];

/* Canonical code of the group element represented by the matrix [[a,b],[c,e]]. */
static int canon_code(int type, int q, int a, int b, int c, int e) {
    if (type == 1) {
        int c1 = ((a * q + b) * q + c) * q + e;
        int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
        int c2 = ((na * q + nb) * q + nc) * q + ne;
        return c1 < c2 ? c1 : c2;
    }
    if (type == 2) {
        int v[4] = {a, b, c, e};
        int f = 0;
        for (int i = 0; i < 4; i++) if (v[i]) { f = v[i]; break; }
        int inv = (int)powmod(f, q - 2, q);
        for (int i = 0; i < 4; i++) v[i] = (v[i] * inv) % q;
        return ((v[0] * q + v[1]) * q + v[2]) * q + v[3];
    }
    return ((a * q + b) * q + c) * q + e;
}

static void set_group(int type, int q) {
    if (type == gm_type && q == gm_q) return;
    gm_type = type;
    gm_q = q;
    int QQ = q * q * q * q;
    for (int i = 0; i < QQ; i++) IDX[i] = -1;
    int N = 0;
    for (int a = 0; a < q; a++)
    for (int b = 0; b < q; b++)
    for (int c = 0; c < q; c++)
    for (int e = 0; e < q; e++) {
        int det = ((a * e - b * c) % q + q) % q;
        if (type == 2 ? det == 0 : det != 1) continue;
        int own = ((a * q + b) * q + c) * q + e;
        if (canon_code(type, q, a, b, c, e) != own) continue;
        if (N >= MAXN) return;
        IDX[own] = N;
        EA[N] = a; EB[N] = b; EC[N] = c; EE[N] = e;
        N++;
    }
    gm_N = N;
}

static int gmul(int x, int y) {
    int q = gm_q;
    int a = EA[x], b = EB[x], c = EC[x], e = EE[x];
    int f = EA[y], g = EB[y], h = EC[y], k = EE[y];
    int r00 = (a * f + b * h) % q;
    int r01 = (a * g + b * k) % q;
    int r10 = (c * f + e * h) % q;
    int r11 = (c * g + e * k) % q;
    return IDX[canon_code(gm_type, q, r00, r01, r10, r11)];
}

/* ---- configurations: (group, fibres p per side) with order 2pN ---- */

static Cfg cfg[MAXCFG];
static int ncfg = 0;
static int fails[MAXCFG];

static void make_configs(void) {
    static const int qs[] = {3, 5, 7, 11, 13, 17};
    ncfg = 0;
    for (int type = 0; type < 3; type++)
        for (int qi = 0; qi < 6; qi++) {
            int q = qs[qi];
            long ord = (long)q * (long)(q * q - 1);
            if (type == 1) ord /= 2;
            if (ord > MAXN) continue;
            int N = (int)ord;
            if (N < d) continue;
            for (int p = 1; p <= MAXP; p++) {
                long T = 2L * p * N;
                if (T > MOORE || T > MAXN) break;
                if (ncfg >= MAXCFG) return;
                cfg[ncfg].type = type;
                cfg[ncfg].q = q;
                cfg[ncfg].p = p;
                cfg[ncfg].N = N;
                cfg[ncfg].T = (int)T;
                ncfg++;
            }
        }
}

/* ---- lifts: A-fibre i element x -> i*N + x; B-fibre j element y -> (p+j)*N + y. ---- */

static int di[MAXDART], dj[MAXDART], dg[MAXDART];

static void make_darts(int p) {
    int nd = 0;
    for (int s = 0; s < d; s++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < p; i++) { di[nd] = i; dj[nd] = perm[i]; nd++; }
    }
}

static int clashes(int t, int g, int nd) {
    for (int s = 0; s < nd; s++)
        if (s != t && di[s] == di[t] && dj[s] == dj[t] && dg[s] == g) return 1;
    return 0;
}

static void build_lift(Graph *g, int p, int N, int nd) {
    int S = p * N;
    g->n = 2 * S;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= S; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, di[t] * N + x, S + dj[t] * N + gmul(x, dg[t]));
}

static int dist_buf[MAXN], queue_buf[MAXN];

/* Left multiplication by the group is a fibre-regular automorphism, so the diameter is at most D
 * iff BFS from element 0 of every fibre (2p sources) reaches everything within D. */
static long orbit_bad(const Graph *g, int p, int N) {
    int nv = g->n;
    long total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        for (int v = 0; v < nv; v++) dist_buf[v] = -1;
        int head = 0, tail = 0;
        dist_buf[src] = 0;
        queue_buf[tail++] = src;
        while (head < tail) {
            int v = queue_buf[head++];
            if (dist_buf[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist_buf[u] < 0) {
                    dist_buf[u] = dist_buf[v] + 1;
                    queue_buf[tail++] = u;
                }
            }
        }
        total += nv - tail;
    }
    return total;
}

/* Anneal voltages with single and pair moves; leaves dg and g at the best assignment seen. */
static long anneal(Graph *g, int p, int N, int nd, int maxit, double until) {
    static int bestdg[MAXDART];
    build_lift(g, p, N, nd);
    long bad = orbit_bad(g, p, N);
    long bestbad = bad;
    memcpy(bestdg, dg, sizeof(int) * nd);
    for (int it = 0; it < maxit && bestbad > 0; it++) {
        if ((it & 31) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dg[t];
        int ng = rndint(N);
        if (ng == old || clashes(t, ng, nd)) continue;
        dg[t] = ng;
        int t2 = -1, old2 = 0;
        if (rndint(4) == 0) {
            t2 = rndint(nd);
            if (t2 == t) t2 = -1;
        }
        if (t2 >= 0) {
            old2 = dg[t2];
            int ng2 = rndint(N);
            if (ng2 == old2 || clashes(t2, ng2, nd)) { dg[t] = old; continue; }
            dg[t2] = ng2;
        }
        build_lift(g, p, N, nd);
        long nb = orbit_bad(g, p, N);
        double temp = 0.5 + 0.02 * (double)bad;
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / temp)) {
            bad = nb;
            if (bad < bestbad) {
                bestbad = bad;
                memcpy(bestdg, dg, sizeof(int) * nd);
            }
        } else {
            dg[t] = old;
            if (t2 >= 0) dg[t2] = old2;
        }
    }
    memcpy(dg, bestdg, sizeof(int) * nd);
    build_lift(g, p, N, nd);
    return bestbad;
}

/* Random base multigraphs and voltages for one configuration until the slice ends. */
static int attempt(Graph *best, int ci, double until) {
    static Graph cand;
    Cfg c = cfg[ci];
    set_group(c.type, c.q);
    if (gm_N != c.N) return 0;
    int p = c.p, N = c.N, nd = p * d;
    while (now() < until) {
        make_darts(p);
        for (int t = 0; t < nd; t++) dg[t] = -1;
        for (int t = 0; t < nd; t++) {
            int g;
            do { g = rndint(N); } while (clashes(t, g, nd));
            dg[t] = g;
        }
        long bad = anneal(&cand, p, N, nd, 15000, until);
        if (bad == 0 && cand.n > best->n && is_valid(&cand)) {
            copy_graph(best, &cand);
            return 1;
        }
    }
    return 0;
}

/* Pick the configuration with the fewest failed slices above the current best (ties: smallest). */
static void search(Graph *best, double until) {
    while (now() < until) {
        int bi = -1;
        for (int c = 0; c < ncfg; c++) {
            if (cfg[c].T <= best->n || cfg[c].T > MOORE) continue;
            if (bi < 0 || fails[c] < fails[bi] ||
                (fails[c] == fails[bi] && cfg[c].T < cfg[bi].T))
                bi = c;
        }
        if (bi < 0) return;
        double left = until - now();
        double sl = left / 6;
        if (sl < 0.4) sl = 0.4;
        if (sl > 5.0) sl = 5.0;
        if (sl > left) sl = left;
        if (!attempt(best, bi, now() + sl)) fails[bi]++;
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

    static Graph best;
    if (d < 2 || d > MAXD || D < 2) {
        printf("2 1\n0 1\n");
        return 0;
    }
    MOORE = moore_bound();
    read_start(&best);
    if (best.n == 0 || !is_valid(&best)) complete_bipartite(&best);
    if (!is_valid(&best)) {
        printf("2 1\n0 1\n");
        return 0;
    }
    make_configs();
    if (best.n < MOORE) search(&best, t_end);
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 4)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
