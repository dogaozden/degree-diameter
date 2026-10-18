"""Bi-Cayley engine with a grow-by-two finish.

Exact families (PG(2,q), Araujo-Pardo-Lopez, W(q)) are used where they apply.
Otherwise the C engine runs simulated annealing over vertex-transitive bi-Cayley
graphs: two sides, each a copy of a group G = Z_m x| Z_k, with base orbits and
voltages chosen so that a few BFS runs from block representatives certify the
diameter for the whole graph. The best graph is then grown by two vertices at a
time with a repair annealer. K_{d,d} is the safe fallback.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions.
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
# C engine: bi-Cayley annealing, then grow-by-two repair.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bipartite degree-diameter engine.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid start), or "0 0".
 * stdout: "n m" + edge lines, the largest valid graph found.
 *
 * Phase 1: bi-Cayley annealing. Side A has kb blocks of G, side B has kb blocks
 * of G, with G = Z_m x| Z_K acting by left multiplication. Layer l joins A-block i
 * to B-block perm[l][i] by A_{i,x} ~ B_{perm,x*s}. Left multiplication is an
 * automorphism that is transitive on each block, so the diameter check needs only
 * BFS from one representative per block.
 * Phase 2: grow by two vertices with a repair annealer.
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
#define MAXK 2
#define PEN 50

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

/* Number of unordered pairs at distance > D. Fills badv[v] with v's bad partners. */
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

/* ---------------- groups: Z_m x|_r Z_K, element a*K+b, (a,b)(c,e) = (a + r^b c, b+e). */

typedef struct {
    int m, K, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->K, b = x % G->K, c = y / G->K, e = y % G->K;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->K + (b + e) % G->K;
}

static int ginv(const Grp *G, int x) {
    int a = x / G->K, b = x % G->K;
    int nb = (G->K - b) % G->K;
    long t = ((long)G->rp[nb] * a) % G->m;
    int na = (int)((G->m - t) % G->m);
    return na * G->K + nb;
}

static void grp_set(Grp *G, int m, int K, int r) {
    G->m = m; G->K = K; G->r = r;
    G->rp[0] = 1 % m;
    for (int b = 1; b < K; b++) G->rp[b] = (int)((long)G->rp[b - 1] * r % m);
}

/* Uniform choice among all semidirect products of order N (reservoir sampling). */
static int choose_group(int N, Grp *G) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int K = N / m;
        if (m == 1) {
            count++;
            if (rndint((int)count) == 0) grp_set(G, 1, K, 0);
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, K, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) grp_set(G, m, K, r);
        }
    }
    return count > 0;
}

/* ---------------- bi-Cayley state. */

static Grp Gr;
static int kb, Nn;                 /* base orbits per side, group order */
static int perm[MAXD][MAXK];       /* layer l: A-block i -> B-block perm[l][i] */
static int volt[MAXD][MAXK];       /* layer l, A-block i: voltage */
static int nbr[MAXN][MAXD];
static int dist_[MAXN], queue_[MAXN];

/* Recompute the neighbours of A-block i and of the B-block it hits in layer l. */
static void refresh(int l, int i) {
    int j = perm[l][i], s = volt[l][i];
    int si = ginv(&Gr, s);
    int A0 = i * Nn, B0 = (kb + j) * Nn;
    for (int x = 0; x < Nn; x++) {
        nbr[A0 + x][l] = B0 + gmul(&Gr, x, s);
        nbr[B0 + x][l] = A0 + gmul(&Gr, x, si);
    }
}

static void init_state(void) {
    for (int l = 0; l < d; l++) {
        if (kb == 1) {
            perm[l][0] = 0;
        } else {
            int p = rndint(2);
            perm[l][0] = p;
            perm[l][1] = 1 - p;
        }
        for (int i = 0; i < kb; i++) volt[l][i] = rndint(Nn);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < kb; i++) refresh(l, i);
}

static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < kb; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1][i] == perm[l2][i] && volt[l1][i] == volt[l2][i]) c++;
    return c;
}

/* Vertices not within distance D of src, counted over the whole graph. */
static long unreached_from(int src) {
    int Nt = 2 * kb * Nn;
    for (int v = 0; v < Nt; v++) dist_[v] = -1;
    int head = 0, tail = 0;
    dist_[src] = 0;
    queue_[tail++] = src;
    while (head < tail) {
        int v = queue_[head++];
        if (dist_[v] >= D) continue;
        for (int l = 0; l < d; l++) {
            int u = nbr[v][l];
            if (dist_[u] < 0) {
                dist_[u] = dist_[v] + 1;
                queue_[tail++] = u;
            }
        }
    }
    return Nt - tail;
}

static long cayley_cost(void) {
    long c = PEN * dup_count();
    for (int b = 0; b < 2 * kb; b++) c += unreached_from(b * Nn);
    return c;
}

static int cayley_sa(double until, long max_steps) {
    init_state();
    long cost = cayley_cost();
    long best_c = cost, last_imp = 0;
    double T0 = 1.0 + 0.1 * (double)cost;
    for (long t = 0; t < max_steps && cost > 0; t++) {
        if ((t & 63) == 0 && now() > until) break;
        if (t - last_imp > max_steps / 3) break;
        double T = T0 * (1.0 - (double)t / (double)max_steps) + 0.05;
        if (kb == 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int tmp = perm[l][0]; perm[l][0] = perm[l][1]; perm[l][1] = tmp;
            refresh(l, 0);
            refresh(l, 1);
            long c2 = cayley_cost();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) {
                cost = c2;
            } else {
                tmp = perm[l][0]; perm[l][0] = perm[l][1]; perm[l][1] = tmp;
                refresh(l, 0);
                refresh(l, 1);
            }
        } else {
            int l = rndint(d), i = rndint(kb);
            int old = volt[l][i];
            int nv = rndint(Nn);
            if (nv == old) continue;
            volt[l][i] = nv;
            refresh(l, i);
            long c2 = cayley_cost();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) {
                cost = c2;
            } else {
                volt[l][i] = old;
                refresh(l, i);
            }
        }
        if (cost < best_c) { best_c = cost; last_imp = t; }
    }
    return cost == 0;
}

static void graph_from_cayley(Graph *g) {
    int A = kb * Nn;
    g->n = 2 * A;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= A; }
    for (int a = 0; a < A; a++)
        for (int l = 0; l < d; l++) add_edge(g, a, nbr[a][l]);
}

static void cayley_phase(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    while (now() < until) {
        int kbt = rnd01() < 0.3 ? 2 : 1;
        int N = best->n / (2 * kbt) + 1 + rndint(3);
        if (2L * kbt * N > moore || 2L * kbt * N > MAXN) {
            kbt = 1;
            N = best->n / 2 + 1 + rndint(3);
        }
        if (N < d) N = d;
        if (2L * kbt * N > moore || 2L * kbt * N > MAXN) break;
        kb = kbt;
        Nn = N;
        if (!choose_group(Nn, &Gr)) continue;
        if (cayley_sa(until, 40000)) {
            graph_from_cayley(&cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ---------------- grow by two vertices with a repair annealer. */

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
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2) {
        double split = t0 + (t_end - t0) * 0.6;
        cayley_phase(&best, split);
        if (best.n > 0) grow_search(&best, t_end);
    }
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
    usable = max(1.0, 0.8 * time_limit - 3.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

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

    # Search: C bi-Cayley annealing, then grow-by-two repair.
    if D >= 2:
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=best, timeout=c_budget + 6)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
