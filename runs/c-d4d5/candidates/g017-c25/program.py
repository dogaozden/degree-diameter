"""Combined program: algebraic starts (PG(2,q), W(q), Araujo-Pardo-Lopez, K_{d,d}) plus a C search.

New in this version: a generic group library for voltage lifts. The C engine receives a list of
group descriptors (direct products of up to three factors from: cyclic Z_n, semidirect
Z_m x|_r Z_k, wreath Z_m wr Z_k, Heisenberg groups over Z_m). Orders are restricted to what
lifts need, so non-metacyclic groups such as Z_3 wr Z_3 (order 81), rank-3 abelian groups and
Heisenberg groups are now available as voltage groups. Lifts use left-regular fibre actions,
so the orbit-reduced diameter test (BFS from the 2p fibre representatives) stays exact for
non-abelian groups.
"""
import itertools
import math
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:   prog d D seed time_limit [group descriptors...] < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * argv[5+]: one group per argument: "nf t a b c [t a b c ...]" with factor types
 *           0 = cyclic Z_a, 1 = semidirect Z_a x|_c Z_b, 2 = wreath Z_a wr Z_b, 3 = Heisenberg(Z_a).
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
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
#define MAXG 256
#define MAXGROUPS 8000

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

/* All-pairs check by bitsets: number of unordered pairs at distance > D. */
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

/* Saturation: adding an A-B edge between vertices with spare degree never increases a distance. */
static int saturate(Graph *g) {
    int added = 0;
    for (int a = 0; a < g->n; a++) {
        if (g->side[a] != 0 || g->deg[a] >= d) continue;
        for (int b = 0; b < g->n && g->deg[a] < d; b++) {
            if (g->side[b] != 1 || g->deg[b] >= d || has_edge(g, a, b)) continue;
            add_edge(g, a, b);
            added++;
        }
    }
    return added;
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

/* ---------------------------------------------------------------- groups
 * A group is a direct product of up to three factors. Element index is mixed radix over the
 * factor orders; index 0 is the identity. */
typedef struct {
    int nf;
    int ft[3], fa[3], fb[3], fc[3];
    int fo[3], stride[3];
    int N;
} Grp;

static Grp groups[MAXGROUPS];
static int ngroups = 0;
static int curN = 1;
static int mtab[MAXG * MAXG];

static int factor_order(int t, int a, int b) {
    long r;
    switch (t) {
    case 0: return a <= MAXG ? a : 0;
    case 1: r = (long)a * b; break;
    case 2: {
        r = 1;
        for (int i = 0; i < b; i++) { r *= a; if (r > MAXG) return 0; }
        r *= b;
        break;
    }
    case 3: r = (long)a * a * a; break;
    default: return 0;
    }
    return r <= MAXG ? (int)r : 0;
}

/* Multiplication inside one factor. */
static int local_mul(int t, int a, int b, int c, int x, int y) {
    if (t == 0) return (x + y) % a;
    if (t == 1) {
        /* Z_a x|_c Z_b: element i*b + j, (i,j)(i',j') = (i + c^j i', j + j'). */
        int m = a, k = b, r = c;
        int x1 = x / k, x2 = x % k, y1 = y / k, y2 = y % k;
        int rp = 1 % m;
        for (int i = 0; i < x2; i++) rp = rp * r % m;
        return ((x1 + rp * y1) % m) * k + (x2 + y2) % k;
    }
    if (t == 2) {
        /* Z_a wr Z_b: element (v, s), v in Z_a^b encoded base a, s in Z_b.
         * (v,s)(w,u) = (v + shift^s(w), s + u), shift^s(w)_i = w_{i-s}. */
        int m = a, k = b, sx = x % k, sy = y % k;
        int vx = x / k, vy = y / k;
        int dx[8], dy[8], res = 0, pw = 1;
        for (int i = 0; i < k; i++) {
            dx[i] = vx % m; vx /= m;
            dy[i] = vy % m; vy /= m;
        }
        for (int i = 0; i < k; i++) {
            int j = ((i - sx) % k + k) % k;
            res += ((dx[i] + dy[j]) % m) * pw;
            pw *= m;
        }
        return res * k + (sx + sy) % k;
    }
    /* t == 3: Heisenberg group over Z_a, (p,q,r)(p',q',r') = (p+p', q+q', r+r'+p q'). */
    {
        int m = a;
        int a1 = x / (m * m), b1 = (x / m) % m, c1 = x % m;
        int a2 = y / (m * m), b2 = (y / m) % m, c2 = y % m;
        int A = (a1 + a2) % m, B = (b1 + b2) % m, C = (c1 + c2 + a1 * b2) % m;
        return (A * m + B) * m + C;
    }
}

static int gmul_idx(const Grp *G, int x, int y) {
    int res = 0;
    for (int f = 0; f < G->nf; f++) {
        int o = G->fo[f];
        int xf = (x / G->stride[f]) % o, yf = (y / G->stride[f]) % o;
        int zf = local_mul(G->ft[f], G->fa[f], G->fb[f], G->fc[f], xf, yf);
        res += zf * G->stride[f];
    }
    return res;
}

static void load_group(const Grp *G) {
    curN = G->N;
    for (int x = 0; x < curN; x++)
        for (int y = 0; y < curN; y++)
            mtab[x * curN + y] = gmul_idx(G, x, y);
}

static int gmul(int x, int y) { return mtab[x * curN + y]; }

static int parse_group(const char *s, Grp *G) {
    const char *q = s;
    char *e;
    long v = strtol(q, &e, 10);
    if (e == q || v < 1 || v > 3) return 0;
    q = e;
    G->nf = (int)v;
    int N = 1;
    for (int f = 0; f < G->nf; f++) {
        long w[4];
        for (int c = 0; c < 4; c++) {
            w[c] = strtol(q, &e, 10);
            if (e == q) return 0;
            q = e;
        }
        int t = (int)w[0], a = (int)w[1], b = (int)w[2], c3 = (int)w[3];
        if (t < 0 || t > 3 || a < 1 || a > MAXG) return 0;
        if (t == 1 && (b < 1 || c3 < 0 || c3 >= MAXG)) return 0;
        if (t == 2 && (b < 1 || b > 8)) return 0;
        int o = factor_order(t, a, b);
        if (o < 1) return 0;
        G->ft[f] = t; G->fa[f] = a; G->fb[f] = b; G->fc[f] = c3;
        G->fo[f] = o;
        G->stride[f] = N;
        N *= o;
        if (N > MAXG) return 0;
    }
    G->N = N;
    return N >= 2;
}

/* ---------------------------------------------------------------- lifts */
typedef struct { int i, j, g; } Dart;

/* Random d-regular bipartite base multigraph on p + p vertices, connected. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) { int j = rndint(i + 1); int s = perm[i]; perm[i] = perm[j]; perm[j] = s; }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, nseen = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) { seen[u] = 1; nseen++; stack[top++] = u; }
            }
        }
        if (nseen == 2 * p) return;
    }
}

/* Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x. */
static void build_lift(Graph *g, int p, const Dart *dt, int nd) {
    int N = curN;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(x, dt[t].g));
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j) {
    int N = curN;
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Orbit-reduced diameter objective. Left multiplication by h on every fibre is an automorphism
 * of a lift with left-regular fibres, so dist((a,x),(b,y)) = dist((a,e),(b,x^-1 y)). BFS from the
 * 2p fibre identities suffices; the count is zero exactly when the lift has diameter <= D. */
static int dist_buf[MAXN], queue_buf[MAXN];

static long orbit_bad(const Graph *g, int p) {
    int nv = g->n;
    int N = curN;
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

/* Hill-climb the voltages of one random base multigraph over the currently loaded group. */
static int lift_fast_try(Graph *g, int p, int steps, double until) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i; dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j);
                nd++;
            }
    build_lift(g, p, dt, nd);
    long bad = orbit_bad(g, p);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j);
        build_lift(g, p, dt, nd);
        long nb = orbit_bad(g, p);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
    }
    build_lift(g, p, dt, nd);
    return bad == 0;
}

/* Search lifts strictly larger than the current best. Groups are drawn from the descriptor
 * list, preferring orders just above what the target needs. */
static void fast_lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    if (ngroups == 0) return;
    while (now() < until) {
        int r = rndint(20);
        int p = r < 8 ? 1 : r < 14 ? 2 : r < 18 ? 3 : 4;
        long target = best->n + 2;
        if (target > moore) return;
        long Nmin = (target + 2 * p - 1) / (2 * p);
        long Nmax = moore / (2 * p);
        if (Nmax > MAXN / (2 * p)) Nmax = MAXN / (2 * p);
        if (Nmin < d) Nmin = d;
        if (Nmin > Nmax) continue;
        int pick = -1;
        for (int pass = 0; pass < 2 && pick < 0; pass++) {
            int cnt = 0;
            for (int i = 0; i < ngroups; i++) {
                long N = groups[i].N;
                if (N < Nmin || N > Nmax) continue;
                if (pass == 0 && N > Nmin + 3) continue;
                cnt++;
                if (rndint(cnt) == 0) pick = i;
            }
        }
        if (pick < 0) continue;
        load_group(&groups[pick]);
        for (int a = 0; a < 3 && now() < until; a++) {
            if (lift_fast_try(&cand, p, 20000, until) && is_valid(&cand) &&
                cand.n > best->n) {
                saturate(&cand);
                copy_graph(best, &cand);
                break;
            }
        }
    }
}

/* ---------------------------------------------------------------- growth */
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
    if (!is_valid(work)) return 0;
    saturate(work);
    return 1;
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
        fprintf(stderr, "usage: %s d D seed time_limit [groups...] < start_graph\n", argv[0]);
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

    for (int i = 5; i < argc && ngroups < MAXGROUPS; i++) {
        Grp G;
        if (parse_group(argv[i], &G)) groups[ngroups++] = G;
    }

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);

    if (best.n > 0) {
        saturate(&best);
        if (!is_valid(&best)) read_start(&best);
    }

    if (D >= 2 && best.n > 0 && best.n < moore_bound()) {
        fast_lift_search(&best, t0 + (t_end - t0) * 0.8);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
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


# ---------------------------------------------------------------- group library

def _factor_order(f):
    t, a, b, c = f
    if t == 0:
        return a
    if t == 1:
        return a * b
    if t == 2:
        return a ** b * b
    return a ** 3


def _order_of(fs):
    o = 1
    for f in fs:
        o *= _factor_order(f)
    return o


def group_descriptors(hi):
    """Descriptors of groups of order 2..hi: cyclic, semidirect, rank-3 abelian, wreath,
    Heisenberg, and each non-cyclic factor times a cyclic group. Each is a list of factors
    (type, a, b, c)."""
    seen, out, base = set(), [], []

    def add(fs):
        key = tuple(fs)
        if key in seen or not (2 <= _order_of(fs) <= hi):
            return False
        seen.add(key)
        out.append(list(fs))
        return True

    for N in range(2, hi + 1):
        add([(0, N, 0, 0)])
        for m in range(2, N + 1):
            if N % m:
                continue
            k = N // m
            if k == 1:
                continue
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    f = (1, m, k, r)
                    if add([f]):
                        base.append(f)
        for a in range(2, N + 1):
            if N % a:
                continue
            for b in range(a, N // a + 1):
                if (N // a) % b:
                    continue
                c = N // (a * b)
                if c >= b and c >= 2:
                    add([(0, a, 0, 0), (0, b, 0, 0), (0, c, 0, 0)])

    for m in range(2, hi + 1):
        for k in range(2, 9):
            if m ** k * k > hi:
                break
            f = (2, m, k, 0)
            if add([f]):
                base.append(f)
    for m in range(2, hi + 1):
        if m ** 3 > hi:
            break
        f = (3, m, 0, 0)
        if add([f]):
            base.append(f)

    for g in list(base):
        o = _factor_order(g)
        for n in range(2, hi // o + 1):
            add([g, (0, n, 0, 0)])
    return out


def _encode(fs):
    parts = [str(len(fs))]
    for f in fs:
        parts += [str(x) for x in f]
    return " ".join(parts)


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

    budget = 0.87 * time_limit - (time.monotonic() - t0) - 1.2
    if budget <= 0.2:
        return best

    hi = min(200, lib.moore_bound(d, D) // 2)
    descs = [_encode(fs) for fs in group_descriptors(hi)] if hi >= 2 else []
    args = [d, D, seed, budget] + descs[:5000]
    try:
        text = lib.run_c(C_SOURCE, args, stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
