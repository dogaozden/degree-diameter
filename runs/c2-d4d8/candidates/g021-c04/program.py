"""Bi-Cayley lifts over finite projective linear groups (PGL(2,q) and PSL(2,q), q prime).

Different construction from the metacyclic parent: the lift base is a p+p fibre multigraph with
d-regular darts, and voltages live in PGL(2,q) or PSL(2,q). Every group element is stored in a
precomputed multiplication table, so the search does not depend on metacyclic presentations.
For example, PGL(2,13) has order 2184, and PSL(2,13) has order 1092 = 2184/2. Left multiplication
is a regular automorphism on each fibre, so the diameter check needs BFS from the 2p fibre
identities only. Successes are verified with a full bitset diameter check.

Fallback: K_{d,d} and the algebraic starts (PG(2,q), Araujo-Pardo-Lopez). The C result is used only
if it validates and is strictly larger.
"""
import time

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
#define MAXP 4
#define MAXDART (MAXD * MAXP)
#define NMAX 2600

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

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
    if (b < 0) b += m;
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

/* ---------- finite group tables: PGL(2,q) (kind 0) or PSL(2,q) (kind 1) ---------- */

static int GN = 0, GID = 0;
static int *MUL = NULL;
static int *IDX = NULL;
static int EL[NMAX][4];
static int gq = 0, gkind = -1;

static int code_of(long a, long b, long c, long e, int q) {
    return (int)(((a * q + b) * q + c) * q + e);
}

static int build_group(int q, int kind) {
    free(MUL); MUL = NULL;
    free(IDX); IDX = NULL;
    GN = 0; gq = 0; gkind = -1;
    int Q4 = q * q * q * q;
    IDX = malloc(sizeof(int) * (size_t)Q4);
    for (int i = 0; i < Q4; i++) IDX[i] = -1;
    int cnt = 0;
    for (int a = 0; a < q; a++)
    for (int b = 0; b < q; b++)
    for (int c = 0; c < q; c++)
    for (int e = 0; e < q; e++) {
        int m[4] = {a, b, c, e};
        int first = -1;
        for (int i = 0; i < 4; i++) if (m[i]) { first = m[i]; break; }
        if (first != 1) continue;
        int det = ((a * e - b * c) % q + q) % q;
        if (det == 0) continue;
        if (kind == 1 && powmod(det, (q - 1) / 2, q) != 1) continue;
        if (cnt >= NMAX) return 0;
        EL[cnt][0] = a; EL[cnt][1] = b; EL[cnt][2] = c; EL[cnt][3] = e;
        IDX[code_of(a, b, c, e, q)] = cnt;
        cnt++;
    }
    GN = cnt;
    MUL = malloc(sizeof(int) * (size_t)GN * GN);
    for (int i = 0; i < GN; i++)
    for (int j = 0; j < GN; j++) {
        long a = EL[i][0], b = EL[i][1], c = EL[i][2], e = EL[i][3];
        long f = EL[j][0], g = EL[j][1], h = EL[j][2], k = EL[j][3];
        long mm[4];
        mm[0] = (a * f + b * h) % q;
        mm[1] = (a * g + b * k) % q;
        mm[2] = (c * f + e * h) % q;
        mm[3] = (c * g + e * k) % q;
        long f0 = -1;
        for (int t = 0; t < 4; t++) if (mm[t]) { f0 = mm[t]; break; }
        if (f0 < 0) { GN = 0; return 0; }
        long s = powmod(f0, q - 2, q);
        for (int t = 0; t < 4; t++) mm[t] = mm[t] * s % q;
        int id = IDX[code_of(mm[0], mm[1], mm[2], mm[3], q)];
        if (id < 0) { GN = 0; return 0; }
        MUL[i * GN + j] = id;
    }
    GID = IDX[code_of(1, 0, 0, 1, q)];
    gq = q;
    gkind = kind;
    return 1;
}

/* ---------- lifts ---------- */

static int nd = 0;
static int di[MAXDART], dj[MAXDART], dg[MAXDART];

static void make_darts(int p) {
    nd = 0;
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

static int clashes(int t, int g) {
    for (int s = 0; s < nd; s++)
        if (s != t && di[s] == di[t] && dj[s] == dj[t] && dg[s] == g) return 1;
    return 0;
}

/* A fibre i element x -> i*GN + x; B fibre j element x -> (p+j)*GN + x. Edge (i,x)-(j, x*g). */
static void build_lift(Graph *g, int p) {
    int S = p * GN;
    g->n = 2 * S;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= S; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < GN; x++)
            add_edge(g, di[t] * GN + x, S + dj[t] * GN + MUL[x * GN + dg[t]]);
}

static int dist_buf[MAXN], queue_buf[MAXN];

/* Left multiplication is a regular automorphism on each fibre: BFS from each fibre identity. */
static long orbit_bad(const Graph *g, int p) {
    int nv = g->n;
    long total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * GN + GID;
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

static long anneal(Graph *g, int p, int maxit, double until) {
    build_lift(g, p);
    long bad = orbit_bad(g, p);
    double T = 1.0;
    for (int it = 0; it < maxit && bad > 0; it++) {
        if ((it & 63) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dg[t];
        int ng = rndint(GN);
        if (ng == old || clashes(t, ng)) continue;
        dg[t] = ng;
        build_lift(g, p);
        long nb = orbit_bad(g, p);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else dg[t] = old;
        T *= 0.999;
        if (T < 0.05) T = 1.0;
    }
    build_lift(g, p);
    return bad;
}

static void attempt(Graph *best, int p, double until) {
    static Graph cand;
    while (now() < until) {
        make_darts(p);
        for (int t = 0; t < nd; t++) dg[t] = -1;
        for (int t = 0; t < nd; t++) {
            int g;
            do { g = rndint(GN); } while (clashes(t, g));
            dg[t] = g;
        }
        long bad = anneal(&cand, p, 8000, until);
        if (bad == 0 && cand.n > best->n && is_valid(&cand)) {
            copy_graph(best, &cand);
            return;
        }
    }
}

static void search(Graph *best, double until) {
    static const int QS[6] = {3, 5, 7, 11, 13, 17};
    while (now() < until) {
        int cq[48], ck[48], cp[48], cn2[48], cnt = 0;
        for (int qi = 0; qi < 6; qi++)
        for (int k = 0; k < 2; k++)
        for (int p = 1; p <= MAXP; p++) {
            long q = QS[qi];
            long N = q * q * q - q;
            if (k == 1) N /= 2;
            long n2 = 2L * p * N;
            if (N < d || N > NMAX || n2 > MOORE || n2 > MAXN || n2 <= best->n) continue;
            cq[cnt] = QS[qi]; ck[cnt] = k; cp[cnt] = p; cn2[cnt] = (int)n2;
            cnt++;
        }
        if (cnt == 0) return;
        int pick;
        if (rndint(2) == 0) {
            pick = 0;
            for (int i = 1; i < cnt; i++) if (cn2[i] > cn2[pick]) pick = i;
        } else {
            pick = rndint(cnt);
        }
        if (cq[pick] != gq || ck[pick] != gkind) {
            if (!build_group(cq[pick], ck[pick])) return;
        }
        double left = until - now();
        if (left <= 0) return;
        double sl = left < 4.0 ? left : 4.0;
        attempt(best, cp[pick], now() + sl);
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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) {
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    MOORE = moore_bound();
    read_start(&best);
    if (best.n == 0 || !is_valid(&best)) complete_bipartite(&best);

    if (D >= 2 && d >= 3 && best.n < MOORE) search(&best, t_end);

    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
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

    # Safe fallback: K_{d,d}, upgraded by any valid algebraic start.
    best = lib.haar_graph(d, range(d))
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 6)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
