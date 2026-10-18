"""Bold variant: group-level bi-Cayley lift annealing (fast rep-BFS cost) plus grow-by-two repair."""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact and small constructions (calibration cases return immediately).
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
# C engine: bi-Cayley lifts over semidirect products Z_m x| Z_k, annealed with a
# cost that only BFSes from one representative per block (exact by vertex
# transitivity of the left group action). Then grow-by-two repair.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid start), or "0 0".
 * stdout: "n m" + edge lines, the largest valid graph found.
 */
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
#define MAXP 4

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
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

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

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

/* Number of unordered pairs at distance > D. */
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

/* ---- groups Z_m x|_r Z_k: element (a,b) = a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k) ---- */
typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

static int random_group(int N, Grp *G) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)(count < 2000000000L ? count : 2000000000L)) == 0) {
                G->m = m; G->k = k; G->r = r;
            }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* ---- bi-Cayley lift: p A-blocks and p B-blocks of size N; layer l pairs A_i with
 *      B_{perm[l][i]} through voltage volt[l][i]: A(i,x) ~ B(perm, x*volt).
 *      Every vertex has degree d. Vertex ids: A(i,x) = i*N+x, B(j,y) = (p+j)*N+y. ---- */
typedef struct {
    int p, N;
    Grp G;
    int perm[MAXD][MAXP];
    int volt[MAXD][MAXP];
} Lift;

static int nbrbuf[MAXN * MAXD];
static int mark[MAXN], dep[MAXN], qbuf[MAXN];
static int mark_stamp = 0;

static void build_nbr(const Lift *L) {
    int p = L->p, N = L->N;
    for (int i = 0; i < p; i++)
        for (int x = 0; x < N; x++) {
            int v = i * N + x;
            for (int l = 0; l < d; l++) {
                int j = L->perm[l][i];
                int y = gmul(&L->G, x, L->volt[l][i]);
                int w = (p + j) * N + y;
                nbrbuf[v * d + l] = w;
                nbrbuf[w * d + l] = v;
            }
        }
}

static int dup_count(const Lift *L) {
    int c = 0;
    for (int i = 0; i < L->p; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (L->perm[l1][i] == L->perm[l2][i] && L->volt[l1][i] == L->volt[l2][i]) c++;
    return c;
}

/* Vertices reached from src within Dep steps (BFS on nbrbuf). */
static int reach_count(int src, int Dep) {
    mark_stamp++;
    int head = 0, tail = 0;
    qbuf[tail++] = src;
    mark[src] = mark_stamp;
    dep[src] = 0;
    while (head < tail) {
        int v = qbuf[head++];
        if (dep[v] >= Dep) continue;
        for (int l = 0; l < d; l++) {
            int u = nbrbuf[v * d + l];
            if (mark[u] != mark_stamp) {
                mark[u] = mark_stamp;
                dep[u] = dep[v] + 1;
                qbuf[tail++] = u;
            }
        }
    }
    return tail;
}

/* Left multiplication is an automorphism, so one BFS per block representative is exact. */
static long lift_cost(const Lift *L) {
    long dup = dup_count(L);
    long n = 2L * L->p * L->N;
    build_nbr(L);
    long c = 0;
    for (int b = 0; b < 2 * L->p; b++)
        c += n - reach_count(b * L->N, D);
    return c + 1000L * dup;
}

static void lift_random_init(Lift *L) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < L->p; i++) L->perm[l][i] = i;
        for (int i = L->p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = L->perm[l][i];
            L->perm[l][i] = L->perm[l][j];
            L->perm[l][j] = s;
        }
        for (int i = 0; i < L->p; i++) L->volt[l][i] = rndint(L->N);
    }
}

static int lift_anneal(Lift *L, long steps, double tlim) {
    long c = lift_cost(L);
    double T0 = 3.0;
    for (long t = 0; t < steps && c > 0; t++) {
        if ((t & 63) == 0 && now() > tlim) break;
        double frac = (double)t / (double)steps;
        double T = T0 * (1.0 - frac) + 0.1;
        int l = rndint(d), i = rndint(L->p);
        if (L->p >= 2 && rnd01() < 0.3) {
            int i2 = rndint(L->p);
            if (i2 == i) continue;
            int s = L->perm[l][i];
            L->perm[l][i] = L->perm[l][i2];
            L->perm[l][i2] = s;
            long nc = lift_cost(L);
            if (nc <= c || rnd01() < exp(-(double)(nc - c) / T)) {
                c = nc;
            } else {
                s = L->perm[l][i];
                L->perm[l][i] = L->perm[l][i2];
                L->perm[l][i2] = s;
            }
        } else {
            int old = L->volt[l][i];
            int nv = rndint(L->N);
            if (nv == old) continue;
            L->volt[l][i] = nv;
            long nc = lift_cost(L);
            if (nc <= c || rnd01() < exp(-(double)(nc - c) / T)) c = nc;
            else L->volt[l][i] = old;
        }
    }
    return c == 0;
}

static void lift_to_graph(const Lift *L, Graph *g) {
    int n = 2 * L->p * L->N;
    build_nbr(L);
    g->n = n;
    for (int v = 0; v < n; v++) {
        g->deg[v] = d;
        g->side[v] = (unsigned char)(v >= L->p * L->N);
        for (int l = 0; l < d; l++) g->adj[v][l] = nbrbuf[v * d + l];
    }
}

static void lift_search(Graph *best, double until) {
    static Lift L;
    static Graph cand;
    long cap = moore_bound();
    if (cap > MAXN) cap = MAXN;
    int fails = 0;
    while (now() < until) {
        int p = 1 + rndint(MAXP);
        long nmin = best->n / (2L * p) + 1;
        if (nmin < d) nmin = d;
        long N = nmin + (rnd01() < 0.5 ? 0 : rndint(3));
        if (2L * p * N > cap) {
            if (++fails > 10000) return;
            continue;
        }
        if (!random_group((int)N, &L.G)) continue;
        L.p = p;
        L.N = (int)N;
        lift_random_init(&L);
        double tl = now() + 6.0;
        if (tl > until) tl = until;
        if (lift_anneal(&L, 20000, tl)) {
            lift_to_graph(&L, &cand);
            if (cand.n > best->n && is_valid(&cand)) {
                copy_graph(best, &cand);
                fails = 0;
            }
        }
    }
}

/* ---- grow-by-two repair ---- */
static int cbad[MAXN];
static int blist[MAXN];

static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    long bad = bad_pairs(work);
    memcpy(cbad, badv, sizeof(int) * work->n);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int nbl = 0;
        for (int w = 0; w < work->n; w++)
            if (cbad[w]) blist[nbl++] = w;
        if (nbl == 0) break;
        int v = rnd01() < 0.8 ? blist[rndint(nbl)] : rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        long nb = bad_pairs(work);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
            memcpy(cbad, badv, sizeof(int) * work->n);
        } else {
            del_edge(work, v, t);
            del_edge(work, s, u);
            add_edge(work, v, u);
            add_edge(work, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

static void grow_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
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
    if (d < 1 || D < 1 || d > MAXD) {
        printf("1 0\n");
        return 0;
    }
    read_start(&best);

    if (D >= 2 && best.n < moore_bound()) {
        lift_search(&best, t0 + (t_end - t0) * 0.8);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + max(1.0, 0.9 * time_limit - 4.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Return the new graph if it is a larger valid graph, else None."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return best
        return None

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Search: C engine does bi-Cayley lift annealing, then grow-by-two repair.
    if D >= 2:
        c_budget = end - time.monotonic()
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=best, timeout=c_budget + 4)
                out = lib.parse_graph_text(text)
                consider(out[0], out[1])
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
