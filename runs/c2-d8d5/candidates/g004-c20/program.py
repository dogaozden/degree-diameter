"""Voltage-lift search over semidirect groups, orbit-reduced in C, followed by grow-by-two.

Python builds exact constructions (projective planes, Araujo-Pardo--Lopez, W(q)) as starts.
C searches bi-Cayley-type lifts: base size P <= 6 per side, d perfect-matching layers,
voltages in a random semidirect group Z_m x| Z_k. Reachability is checked from the 2P block
representatives only, because the group acts regularly on each side. If no lift works, the
best graph so far is kept, and grow-by-two then runs on it.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions (calibration cases return immediately).
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
# C engine: orbit-reduced voltage-lift search, then grow-by-two annealing.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid start), or "0 0".
 * stdout: "n m" + edge lines, the largest valid graph found.
 *
 * Lift phase: base P per side, d layers (perfect matchings sig[l]) with voltages vol[l][i]
 * in a semidirect group Z_m x| Z_k of order NG. Left translations are automorphisms, so
 * reachability is checked by BFS from the 2P identity representatives only.
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
#define MAXG 1600
#define MAXP 6
#define PEN 1000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static double phase_end;

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

/* Number of unordered pairs at distance > D. Fills badv[v] = number of bad partners of v. */
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

/* ---------------- groups: Z_m x|_r Z_k, element (a,b) = a*k+b, identity 0 ---------------- */

static int NG;
static int Rt[MAXG * MAXG];   /* Rt[g*NG + x] = x*g */
static int Ginv[MAXG];

/* Choose uniformly among all semidirect parameters (m, k, r) with m*k = N. */
static int choose_group(int N, int *pm, int *pk, int *pr) {
    int cnt = 0, bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            cnt++;
            if (rndint(cnt) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint(cnt) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!cnt) return 0;
    *pm = bm; *pk = bk; *pr = br;
    return 1;
}

static void build_group(int m, int k, int r) {
    int N = m * k;
    int rp[MAXG];
    NG = N;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int g = 0; g < N; g++) {
        int c = g / k, e = g % k;
        for (int x = 0; x < N; x++) {
            int a = x / k, b = x % k;
            Rt[g * N + x] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int g = 0; g < N; g++) {
        Ginv[g] = 0;
        for (int h = 0; h < N; h++)
            if (Rt[h * N + g] == 0) { Ginv[g] = h; break; }
    }
}

/* ---------------- lift state ---------------- */

static int NP;                       /* base size per side */
static int sig[MAXD][MAXP];          /* A_i -> B_{sig[l][i]} */
static int isig[MAXD][MAXP];         /* B_j -> A_{isig[l][j]} */
static int vol[MAXD][MAXP];          /* voltage of dart (l, i) */
static int mark[2 * MAXP * MAXG];
static int bq[2 * MAXP * MAXG];
static int stamp_c = 0;

static void init_state(void) {
    for (int l = 0; l < d; l++) {
        int perm[MAXP];
        for (int i = 0; i < NP; i++) perm[i] = i;
        for (int i = NP - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < NP; i++) {
            sig[l][i] = perm[i];
            isig[l][perm[i]] = i;
            vol[l][i] = rndint(NG);
        }
    }
}

/* Sum over the 2P representatives of the number of vertices at distance > D. */
static long lift_cost(void) {
    int V = 2 * NP * NG;
    long total = 0;
    for (int s = 0; s < 2 * NP; s++) {
        int src = s * NG;
        int head = 0, tail = 0;
        stamp_c++;
        mark[src] = stamp_c;
        bq[tail++] = src;
        for (int lvl = 0; lvl < D && head < tail; lvl++) {
            int lend = tail;
            while (head < lend) {
                int v = bq[head++];
                int blk = v / NG, x = v - blk * NG;
                if (blk < NP) {
                    for (int l = 0; l < d; l++) {
                        int u = (NP + sig[l][blk]) * NG + Rt[vol[l][blk] * NG + x];
                        if (mark[u] != stamp_c) { mark[u] = stamp_c; bq[tail++] = u; }
                    }
                } else {
                    int j = blk - NP;
                    for (int l = 0; l < d; l++) {
                        int i = isig[l][j];
                        int u = i * NG + Rt[Ginv[vol[l][i]] * NG + x];
                        if (mark[u] != stamp_c) { mark[u] = stamp_c; bq[tail++] = u; }
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

/* Parallel darts with the same endpoints and voltage would create multi-edges. */
static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < NP; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (sig[l][i] == sig[l2][i] && vol[l][i] == vol[l2][i]) c++;
    return c;
}

static long run_sa(long steps, long stall) {
    long cost = lift_cost() + PEN * dup_count();
    long c0 = cost, best_c = cost, last = 0;
    double T0 = 1.0 + 0.05 * (double)c0;
    for (long t = 0; t < steps && cost > 0; t++) {
        if ((t & 127) == 0 && now() > phase_end) break;
        if (t - last > stall) break;
        double T = T0 * (1.0 - (double)t / (double)steps) + 0.2;
        int l = rndint(d), i = rndint(NP);
        if (rndint(2) == 0) {
            int old = vol[l][i];
            int nv = rndint(NG);
            if (nv == old) continue;
            vol[l][i] = nv;
            long c2 = lift_cost() + PEN * dup_count();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) cost = c2;
            else vol[l][i] = old;
        } else {
            int i2 = rndint(NP);
            if (i2 == i) continue;
            int j1 = sig[l][i], j2 = sig[l][i2];
            sig[l][i] = j2; sig[l][i2] = j1;
            isig[l][j1] = i2; isig[l][j2] = i;
            long c2 = lift_cost() + PEN * dup_count();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) cost = c2;
            else {
                sig[l][i] = j1; sig[l][i2] = j2;
                isig[l][j1] = i; isig[l][j2] = i2;
            }
        }
        if (cost < best_c) { best_c = cost; last = t; }
    }
    return cost;
}

static void build_explicit(Graph *g) {
    int V = 2 * NP * NG, half = NP * NG;
    g->n = V;
    for (int v = 0; v < V; v++) { g->deg[v] = 0; g->side[v] = v >= half; }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < NP; i++)
            for (int x = 0; x < NG; x++)
                add_edge(g, i * NG + x, (NP + sig[l][i]) * NG + Rt[vol[l][i] * NG + x]);
}

static void lift_phase(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    int fails = 0;
    phase_end = until;
    while (now() < until) {
        int p = rndint(12) == 0 ? 1 : 2 + rndint(5);   /* mostly 2..6 */
        NP = p;
        int N = best->n / (2 * p) + 1 + rndint(3);
        if (best->n == 0) N = d + rndint(3);
        if (N < 1 || N > MAXG || 2L * p * N > moore || 2 * p * N > MAXN) {
            if (++fails > 5000) return;
            continue;
        }
        int m, k, r2;
        if (!choose_group(N, &m, &k, &r2)) continue;
        build_group(m, k, r2);
        init_state();
        long c = run_sa(14000, 3000);
        if (c == 0) {
            build_explicit(&cand);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ---------------- grow-by-two annealing (from the previous engine) ---------------- */

static int bad_list[MAXN];
static int badsave[MAXN];

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
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int nbad = 0;
        for (int w = 0; w < work->n; w++)
            if (badv[w] > 0) bad_list[nbad++] = w;
        int v = nbad ? bad_list[rndint(nbad)] : rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
        memcpy(badsave, badv, sizeof(int) * work->n);
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        long nb = bad_pairs(work);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(work, v, t);
            del_edge(work, s, u);
            add_edge(work, v, u);
            add_edge(work, s, t);
            memcpy(badv, badsave, sizeof(int) * work->n);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

static void grow_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound()) {
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
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && best.n < moore_bound()) {
        double lift_until = t0 + (t_end - t0) * 0.85;
        lift_phase(&best, lift_until);
        grow_search(&best, t_end);
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
    usable = max(1.0, 0.8 * time_limit - 2.0)
    end = t0 + usable

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

    # C engine: voltage-lift search over semidirect groups, then grow-by-two.
    if D >= 2:
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=best, timeout=c_budget + 10)
                out = lib.parse_graph_text(text)
                consider(out[0], out[1])
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
