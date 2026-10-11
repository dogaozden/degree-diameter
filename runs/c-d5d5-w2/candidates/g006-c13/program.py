"""Bipartite degree-diameter search, version 2.

Known constructions give a starting graph. The C engine then searches voltage lifts
over a pool of finite groups supplied as multiplication tables (metacyclic groups and
their direct products with Z_2 or Z_3). Lifts are chosen by orders near the current
target, and the search finishes with grow-by-two annealing. The group tables and the
start graph travel to C inside the stdin edge list, so no extra compile is needed.
"""
import math
import random
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core, group-table lift version.
 *
 * Usage:  prog d D seed time_limit   < input
 * Input:  "0 M" followed by M pairs "u v". The 2M integers form a flat stream:
 *           G, then G groups (N, then N*N table entries, row-major, identity = 0),
 *           then the start graph: n, m, then m edges (u v).
 * Output: "n m" then m lines "u v" for the largest valid graph found.
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
#define MAXGN 512
#define MAXGR 128
#define MAXK 3

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static long moore;
static Graph best;

/* ------------------------------------------------------------------ utilities */

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

static long compute_moore(void) {
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

/* ------------------------------------------------------------------ graph basics */

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

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D (bitset reachability). */
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

/* Full validity: simple, bipartite by side labels, degree <= d, diameter <= D. */
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

/* ------------------------------------------------------------------ input */

static int *IN;
static long INL, INP;
static int INBAD;

static int GN[MAXGR];
static const int *GT[MAXGR];
static int ngr = 0;

static int getv(void) {
    if (INP >= INL) { INBAD = 1; return 0; }
    return IN[INP++];
}

static void load_input(Graph *g) {
    g->n = 0;
    int G = getv();
    if (INBAD || G < 0 || G > 100000) return;
    for (int q = 0; q < G; q++) {
        int N = getv();
        if (INBAD || N < 1 || N > MAXGN || INP + (long)N * N > INL) return;
        const int *T = IN + INP;
        INP += (long)N * N;
        int ok = 1;
        for (long i = 0; i < (long)N * N && ok; i++)
            if (T[i] < 0 || T[i] >= N) ok = 0;
        for (int y = 0; y < N && ok; y++)
            if (T[y] != y || T[(long)y * N] != y) ok = 0;
        if (ok && ngr < MAXGR) { GN[ngr] = N; GT[ngr] = T; ngr++; }
    }
    int sn = getv();
    int sm = getv();
    if (INBAD || sn <= 0 || sn > MAXN || sm < 0 || INP + 2L * sm > INL) return;
    g->n = sn;
    for (int v = 0; v < sn; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (long e = 0; e < sm; e++) {
        int u = IN[INP + 2 * e], v = IN[INP + 2 * e + 1];
        if (u < 0 || v < 0 || u >= sn || v >= sn || u == v ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    INP += 2L * sm;
    static int queue[MAXN];
    for (int s = 0; s < sn; s++) {
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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ lifts */

static int K_, N_, nd_;
static int dI[MAXD * MAXK], dJ[MAXD * MAXK], dS[MAXD * MAXK];
static const int *curT;

static int adjL[MAXN][MAXD];
static int degL[MAXN];
static int visL[MAXN];
static int qL[MAXN];
static int stampL = 0;

/* Cost = 1e6 * duplicate darts + total unreached (representative, vertex) pairs. */
static long lift_cost(void) {
    int k = K_, N = N_, n = 2 * k * N;
    long pen = 0;
    for (int t = 0; t < nd_; t++)
        for (int u = 0; u < t; u++)
            if (dI[t] == dI[u] && dJ[t] == dJ[u] && dS[t] == dS[u]) pen++;
    for (int v = 0; v < n; v++) degL[v] = 0;
    for (int t = 0; t < nd_; t++)
        for (int g = 0; g < N; g++) {
            int a = dI[t] * N + g;
            int b = (k + dJ[t]) * N + curT[g * N + dS[t]];
            adjL[a][degL[a]++] = b;
            adjL[b][degL[b]++] = a;
        }
    long unreached = 0;
    int reps[2 * MAXK], nr = 0;
    for (int i = 0; i < k; i++) reps[nr++] = i * N;
    for (int j = 0; j < k; j++) reps[nr++] = (k + j) * N;
    for (int r = 0; r < nr; r++) {
        stampL++;
        int head = 0, tail = 0;
        int src = reps[r];
        visL[src] = stampL;
        qL[tail++] = src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = qL[head++];
                for (int i = 0; i < degL[u]; i++) {
                    int v = adjL[u][i];
                    if (visL[v] != stampL) { visL[v] = stampL; qL[tail++] = v; }
                }
            }
        }
        unreached += n - tail;
    }
    return pen * 1000000L + unreached;
}

static void build_lift(Graph *g) {
    int k = K_, N = N_;
    g->n = 2 * k * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= k * N; }
    for (int t = 0; t < nd_; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dI[t] * N + x, (k + dJ[t]) * N + curT[x * N + dS[t]]);
}

/* Hill-climb on the darts of a fresh random lift over the current group. */
static int lift_attempt(int steps, double until) {
    int k = K_, N = N_;
    nd_ = d * k;
    int perm[MAXK];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1), s = perm[i];
            perm[i] = perm[j];
            perm[j] = s;
        }
        for (int i = 0; i < k; i++) {
            int t = l * k + i;
            dI[t] = i;
            dJ[t] = perm[i];
            dS[t] = rndint(N);
        }
    }
    long c = lift_cost();
    for (int s = 0; s < steps && c > 0; s++) {
        if ((s & 255) == 0 && now() > until) break;
        if (k > 1 && rnd01() < 0.15) {
            int l = rndint(d), a = rndint(k), b = rndint(k);
            if (a == b) continue;
            int t1 = l * k + a, t2 = l * k + b;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < 0.01) c = c2;
            else { tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp; }
        } else {
            int t = rndint(nd_);
            int old = dS[t];
            dS[t] = rndint(N);
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < 0.01) c = c2;
            else dS[t] = old;
        }
    }
    return c == 0;
}

/* Pick a group whose lift with k sides reaches at least `target` vertices.
   Prefer orders within a few steps of the minimum; otherwise the smallest feasible. */
static int pick_group(int k, long target) {
    long need = (target + 2L * k - 1) / (2L * k);
    int near[MAXGR], nn = 0, far = -1;
    for (int g = 0; g < ngr; g++) {
        long N = GN[g];
        if (N < need) continue;
        if (2L * k * N > moore || 2L * k * N > MAXN) continue;
        if (N <= need + 6) near[nn++] = g;
        if (far < 0 || GN[g] < GN[far]) far = g;
    }
    if (nn > 0) return near[rndint(nn)];
    return far;
}

static void lift_phase(double until) {
    static Graph cand;
    static const int kc[6] = {1, 1, 1, 2, 2, 3};
    int fails = 0;
    if (ngr == 0) return;
    while (now() < until && best.n < moore) {
        int k = kc[rndint(6)];
        int g = pick_group(k, best.n + 2);
        if (g < 0) {
            if (++fails > 200) return;
            continue;
        }
        K_ = k;
        N_ = GN[g];
        curT = GT[g];
        if (lift_attempt(25000, until)) {
            build_lift(&cand);
            if (cand.n > best.n && is_valid(&cand)) copy_graph(&best, &cand);
        }
    }
}

/* ------------------------------------------------------------------ grow by two */

static int grow_once(const Graph *base, Graph *work, double until) {
    int n = base->n;
    if (n + 2 > moore || n + 2 > MAXN) return 0;
    copy_graph(work, base);
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
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
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
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
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

static void grow_search(double until) {
    static Graph work;
    while (now() < until && best.n + 2 <= moore) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(&best, &work, now() + slice)) copy_graph(&best, &work);
    }
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < input\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = compute_moore();

    int hn = 0, hm = 0;
    INL = 0;
    INP = 0;
    INBAD = 0;
    IN = malloc(sizeof(int) * 2);
    if (scanf("%d %d", &hn, &hm) == 2 && hm >= 0 && hm <= 20000000 && IN) {
        free(IN);
        INL = 2L * hm;
        IN = malloc(sizeof(int) * (size_t)(INL > 0 ? INL : 1));
        int ok = IN != NULL;
        for (long i = 0; ok && i < hm; i++)
            if (scanf("%d %d", &IN[2 * i], &IN[2 * i + 1]) != 2) ok = 0;
        if (!ok) INL = 0;
    }
    if (!IN) INL = 0;

    load_input(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (best.n < moore) {
        lift_phase(t0 + (t_end - t0) * 0.75);
        grow_search(t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


_MAX_ORDER = 512        # largest group order the C engine accepts
_ENTRY_BUDGET = 1_000_000   # total group-table entries sent to C
_MAX_GROUPS = 80


def _known_start(d, D):
    """Best directly constructible graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record family 2(q^2+q+5)
    return None


def _tabulate(spec):
    """Return (N, row-major multiplication table) with identity at index 0."""
    if spec[0] == "sd":
        _, m, k, r = spec
        N, mul, _inv = lib.semidirect_group(m, k, r)
        return N, [mul(x, y) for x in range(N) for y in range(N)]
    _, m, k, r, c = spec
    B, bmul, _inv = lib.semidirect_group(m, k, r)
    N = B * c

    def mul(x, y):
        a, z = divmod(x, c)
        b, w = divmod(y, c)
        return bmul(a, b) * c + (z + w) % c

    return N, [mul(x, y) for x in range(N) for y in range(N)]


def _pick_groups(moore, rng):
    """Choose a spread of groups with orders in a window useful for lifts."""
    hi = min(_MAX_ORDER, moore // 2)
    if hi < 1:
        return []
    lo = min(max(1, moore // 12), 300, hi)
    specs = {}
    for N in range(lo, hi + 1):
        lst = []
        for m in range(1, N + 1):
            if N % m:
                continue
            k = N // m
            for r in range(m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    lst.append(("sd", m, k, r))
        if lst:
            specs[N] = lst
    # Direct products with Z_2 or Z_3 give extra orders and non-metacyclic groups.
    for N0, lst0 in list(specs.items()):
        for c in (2, 3):
            M = N0 * c
            if lo <= M <= hi and rng.random() < 0.25:
                _, m, k, r = rng.choice(lst0)
                specs.setdefault(M, []).append(("pd", m, k, r, c))
    orders = list(specs)
    rng.shuffle(orders)
    for lst in specs.values():
        rng.shuffle(lst)
    chosen, used = [], 0
    progress = True
    while progress and len(chosen) < _MAX_GROUPS:
        progress = False
        for N in orders:
            lst = specs[N]
            if not lst or used + N * N > _ENTRY_BUDGET:
                continue
            chosen.append(lst.pop())
            used += N * N
            progress = True
            if len(chosen) >= _MAX_GROUPS:
                break
    return [_tabulate(spec) for spec in chosen]


def _encode(best, groups):
    """Flat integer stream (G, groups, start graph), packed as pairs for lib.run_c."""
    flat = [len(groups)]
    for N, table in groups:
        flat.append(N)
        flat.extend(table)
    n, edges = best
    flat.extend([n, len(edges)])
    for u, v in edges:
        flat.extend((u, v))
    if len(flat) % 2:
        flat.append(0)
    return [(flat[i], flat[i + 1]) for i in range(0, len(flat), 2)]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return (1, [])
    if D == 1:
        return (2, [(0, 1)])

    best = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand

    start = _known_start(d, D)
    if start is not None:
        consider(start)

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 2.0:
        return best

    try:
        rng = random.Random(seed)
        groups = _pick_groups(moore, rng)
        pairs = _encode(best, groups)
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=(0, pairs), timeout=budget + 5)
        consider(lib.parse_graph_text(text))
    except (RuntimeError, ValueError, MemoryError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
