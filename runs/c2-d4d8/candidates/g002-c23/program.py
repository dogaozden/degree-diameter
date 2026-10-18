"""Combined bi-Cayley and voltage-lift search, v3.

Python builds the best algebraic start (PG(2,q), W(q), Araujo-Pardo-Lopez, or K_{d,d}) and
checks it with lib.is_valid. The C engine then:
  1. Searches voltage lifts of small base multigraphs (p fibres per side, d-regular) over
     groups: PSL(2,q)/PGL(2,q) for q in {7,11,13,17} and random semidirect products
     Z_m x| Z_k. The p = 1 case is a bi-Cayley graph. Voltages are annealed with the
     orbit-reduced diameter objective (BFS from the 2p fibre representatives only).
  2. Grows the best graph by two vertices with degree-preserving annealing in the time left.
Every returned graph is re-verified with a full bitset diameter check before it is accepted.
"""
import itertools
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

#define MAXG 2600
#define MAXN 8192
#define MAXW (MAXN / 64)
#define MAXD 12
#define MAXP 12

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
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

/* ---------------- groups as multiplication tables ---------------- */
static int GN, GID;
static uint16_t MT[MAXG * MAXG];
static int GINV[MAXG];

static void finish_group(void) {
    for (int x = 0; x < GN; x++) {
        GINV[x] = -1;
        for (int y = 0; y < GN; y++)
            if (MT[(size_t)x * GN + y] == GID) { GINV[x] = y; break; }
    }
}

/* Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
static int build_semi(int m, int k, int r) {
    if (m < 1 || k < 1 || m * k > MAXG) return 0;
    int N = m * k;
    static int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    GN = N;
    GID = 0;
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            int z = (int)(((long)a + (long)rp[b] * c) % m) * k + (b + e) % k;
            MT[(size_t)x * N + y] = (uint16_t)z;
        }
    }
    finish_group();
    return 1;
}

static int random_semi(int N) {
    long cnt = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        for (int r = 0; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!cnt) return 0;
    return build_semi(bm, bk, br);
}

static int idx_of[17 * 17 * 17 * 17];

static int enc4(const int *v, int q) { return ((v[0] * q + v[1]) * q + v[2]) * q + v[3]; }
static void dec4(int code, int q, int *v) {
    v[3] = code % q; code /= q;
    v[2] = code % q; code /= q;
    v[1] = code % q; code /= q;
    v[0] = code;
}

/* Canonical code: PGL scales the first nonzero entry to 1; PSL takes min(M, -M). q prime. */
static int canon4(const int *v, int q, int psl) {
    int w[4];
    if (!psl) {
        int f = 1;
        for (int i = 0; i < 4; i++) if (v[i]) { f = v[i]; break; }
        int iv = (int)powmod(f, q - 2, q);
        for (int i = 0; i < 4; i++) w[i] = v[i] * iv % q;
        return enc4(w, q);
    }
    int ng[4];
    for (int i = 0; i < 4; i++) ng[i] = (q - v[i]) % q;
    int a = enc4(v, q), b = enc4(ng, q);
    return a < b ? a : b;
}

static int build_linear(int q, int psl) {
    if (q < 3 || q > 17) return 0;
    int total = q * q * q * q;
    for (int c = 0; c < total; c++) idx_of[c] = -1;
    static int elems[MAXG];
    int ne = 0;
    for (int code = 0; code < total; code++) {
        int v[4];
        dec4(code, q, v);
        int det = ((v[0] * v[3] - v[1] * v[2]) % q + q) % q;
        if (psl ? det != 1 : det == 0) continue;
        if (canon4(v, q, psl) != code) continue;
        if (ne >= MAXG) return 0;
        elems[ne] = code;
        idx_of[code] = ne;
        ne++;
    }
    GN = ne;
    int I[4] = {1, 0, 0, 1};
    GID = idx_of[canon4(I, q, psl)];
    for (int i = 0; i < GN; i++) {
        int A[4];
        dec4(elems[i], q, A);
        for (int j = 0; j < GN; j++) {
            int B[4], P[4];
            dec4(elems[j], q, B);
            P[0] = (A[0] * B[0] + A[1] * B[2]) % q;
            P[1] = (A[0] * B[1] + A[1] * B[3]) % q;
            P[2] = (A[2] * B[0] + A[3] * B[2]) % q;
            P[3] = (A[2] * B[1] + A[3] * B[3]) % q;
            MT[(size_t)i * GN + j] = (uint16_t)idx_of[canon4(P, q, psl)];
        }
    }
    finish_group();
    return GN;
}

/* ---------------- graphs ---------------- */
typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}
static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++) if (g->adj[u][i] == v) return 1;
    return 0;
}
static void del_half(Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) { g->adj[u][i] = g->adj[u][--g->deg[u]]; return; }
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

/* Number of unordered pairs at distance > D; fills badv with per-vertex counts. */
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

static int graph_ok(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++) if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

static int read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN || m < 0) return 0;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { g->n = 0; return 0; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || g->deg[u] >= d || g->deg[v] >= d) {
            g->n = 0;
            return 0;
        }
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
                else if (g->side[u] == g->side[v]) { g->n = 0; return 0; }
            }
        }
    }
    if (!graph_ok(g)) { g->n = 0; return 0; }
    return 1;
}

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
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

/* ---------------- voltage lifts ---------------- */
/* Vertex (fibre f, element x) -> f*N + x; A-fibres 0..p-1, B-fibres p..2p-1.
 * Dart t joins A(di,x) to B(dj, x*dg[t]). */
typedef struct {
    int p, N, nd;
    int di[MAXP * MAXD], dj[MAXP * MAXD], dg[MAXP * MAXD], dgi[MAXP * MAXD];
    int Af[MAXP][MAXD], Bf[MAXP][MAXD];
} Lift;

static Lift LF;
static Graph cand;
static int dist_[MAXN], qbuf[MAXN];

static int base_connected(const Lift *L) {
    int p = L->p;
    int seen[2 * MAXP] = {0}, st[2 * MAXP], top = 0, cnt = 1;
    seen[0] = 1;
    st[top++] = 0;
    while (top) {
        int v = st[--top];
        for (int t = 0; t < L->nd; t++) {
            int a = L->di[t], b = p + L->dj[t];
            int u = -1;
            if (v == a) u = b;
            else if (v == b) u = a;
            if (u >= 0 && !seen[u]) { seen[u] = 1; cnt++; st[top++] = u; }
        }
    }
    return cnt == 2 * p;
}

static int voltage_ok(const Lift *L, int t, int g) {
    for (int t2 = 0; t2 < L->nd; t2++)
        if (t2 != t && L->di[t2] == L->di[t] && L->dj[t2] == L->dj[t] && L->dg[t2] == g) return 0;
    return 1;
}

static void set_voltage(Lift *L, int t, int g) {
    L->dg[t] = g;
    L->dgi[t] = GINV[g];
}

static int make_base(Lift *L, int p, int N) {
    if (N < d || p < 1 || p > MAXP) return 0;
    L->p = p;
    L->N = N;
    L->nd = p * d;
    for (int tries = 0;; tries++) {
        if (tries > 200) return 0;
        int t = 0;
        for (int s = 0; s < d; s++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
            }
            for (int i = 0; i < p; i++) { L->di[t] = i; L->dj[t] = perm[i]; t++; }
        }
        if (base_connected(L)) break;
    }
    for (int i = 0; i < p; i++) {
        int c = 0;
        for (int t = 0; t < L->nd; t++) if (L->di[t] == i) L->Af[i][c++] = t;
    }
    for (int j = 0; j < p; j++) {
        int c = 0;
        for (int t = 0; t < L->nd; t++) if (L->dj[t] == j) L->Bf[j][c++] = t;
    }
    for (int t = 0; t < L->nd; t++) {
        int g;
        for (;;) {
            g = rndint(N);
            int clash = 0;
            for (int t2 = 0; t2 < t; t2++)
                if (L->di[t2] == L->di[t] && L->dj[t2] == L->dj[t] && L->dg[t2] == g) { clash = 1; break; }
            if (!clash) break;
        }
        set_voltage(L, t, g);
    }
    return 1;
}

/* Orbit-reduced objective: BFS from the 2p fibre representatives; counts (rep, vertex)
 * pairs at distance > D. Zero means the lift has diameter <= D. */
static int orbit_bad(const Lift *L) {
    int p = L->p, N = L->N, pN = p * N, nv = 2 * pN, total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N + GID;
        for (int v = 0; v < nv; v++) dist_[v] = -1;
        int head = 0, tail = 0;
        dist_[src] = 0;
        qbuf[tail++] = src;
        while (head < tail) {
            int v = qbuf[head++];
            int dv = dist_[v];
            if (dv >= D) continue;
            if (v < pN) {
                int i = v / N, x = v - i * N;
                for (int k = 0; k < d; k++) {
                    int t = L->Af[i][k];
                    int u = pN + L->dj[t] * N + MT[(size_t)x * N + L->dg[t]];
                    if (dist_[u] < 0) { dist_[u] = dv + 1; qbuf[tail++] = u; }
                }
            } else {
                int w = v - pN, j = w / N, y = w - j * N;
                for (int k = 0; k < d; k++) {
                    int t = L->Bf[j][k];
                    int u = L->di[t] * N + MT[(size_t)y * N + L->dgi[t]];
                    if (dist_[u] < 0) { dist_[u] = dv + 1; qbuf[tail++] = u; }
                }
            }
        }
        total += nv - tail;
    }
    return total;
}

static void build_graph_from_lift(Graph *g, const Lift *L) {
    int p = L->p, N = L->N, pN = p * N;
    g->n = 2 * pN;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= pN; }
    for (int t = 0; t < L->nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, L->di[t] * N + x, pN + L->dj[t] * N + MT[(size_t)x * N + L->dg[t]]);
}

static int badlift_budget_ok(long vertices) {
    return vertices <= MAXN;
}

static void lift_search(Graph *best, double until) {
    long moore = moore_bound();
    static const int fams[7][2] = {{11, 1}, {11, 0}, {13, 1}, {13, 0}, {7, 0}, {7, 1}, {17, 1}};
    int built_key = -1;
    while (now() < until) {
        if (best->n + 2 > moore) break;
        int pr = rndint(10);
        int p = pr < 4 ? 1 : (pr < 9 ? 2 + rndint(4) : 6 + rndint(MAXP - 5));
        int N = 0;
        if (rndint(100) < 35) {
            int f = rndint(7);
            int q = fams[f][0], psl = fams[f][1];
            long order = psl ? (long)q * (q * q - 1) / 2 : (long)q * (q * q - 1);
            long nv = 2L * p * order;
            if (nv <= best->n || nv > moore || !badlift_budget_ok(nv)) continue;
            if (built_key != f) {
                if (build_linear(q, psl) != (int)order) { built_key = -1; continue; }
                built_key = f;
            }
            N = (int)order;
        } else {
            long Nt = best->n / (2 * p) + 1 + rndint(4);
            if (Nt < d) Nt = d;
            long nv = 2L * p * Nt;
            if (nv > moore || !badlift_budget_ok(nv) || Nt > MAXG) continue;
            built_key = -1;
            if (!random_semi((int)Nt)) continue;
            N = (int)Nt;
        }
        if (!make_base(&LF, p, N)) continue;
        int bad = orbit_bad(&LF);
        double slice_end = now() + 2.0;
        if (slice_end > until) slice_end = until;
        const long steps = 40000;
        const double T0 = 1.0, T1 = 0.03;
        for (long s = 0; s < steps && bad > 0; s++) {
            if ((s & 255) == 0 && now() > slice_end) break;
            int t = rndint(LF.nd);
            int g = rndint(N);
            if (g == LF.dg[t] || !voltage_ok(&LF, t, g)) continue;
            int old = LF.dg[t], oldi = LF.dgi[t];
            set_voltage(&LF, t, g);
            int nb = orbit_bad(&LF);
            double T = T0 * pow(T1 / T0, (double)s / (double)steps);
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
                bad = nb;
            } else {
                LF.dg[t] = old;
                LF.dgi[t] = oldi;
            }
        }
        if (bad == 0) {
            build_graph_from_lift(&cand, &LF);
            if (cand.n > best->n && graph_ok(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ---------------- grow by two vertices ---------------- */
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
    if (k < d - 1) return 0;
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
    return graph_ok(work);
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
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double t0 = now();
    t_end = t0 + limit * 0.92;

    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    static Graph best;
    if (!read_start(&best)) complete_bipartite(&best);
    if (best.n < moore_bound()) {
        double lift_end = now() + 0.75 * (t_end - now());
        lift_search(&best, lift_end);
        grow_search(&best, t_end);
    }
    if (!graph_ok(&best)) complete_bipartite(&best);
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

    # Safe fallback: K_{d,d} (valid for D >= 2), or a better algebraic start.
    best = lib.haar_graph(d, range(d))
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 12 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
