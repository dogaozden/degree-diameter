"""Non-abelian bi-Cayley lift search plus grow-by-two repair.

Changed in this version: the lift sweep now also draws groups from finite matrix
groups PSL(2,q), SL(2,q), PGL(2,q) (q in 5,7,8,9,11,13), built inside the C engine
from GF(q) arithmetic. These are non-solvable groups, unlike the semidirect products
of the previous version, so this is a substantially different family. Each lift is a
bi-Cayley (Haar-type) graph over the group with a small base multigraph of voltages.
The orbit-reduced BFS check and the full bitset diameter check are kept, and every
output is checked with lib.is_valid. The H(3) incidence graph stays as the start and
the fallback. Semidirect and cyclic groups remain as a second family.
"""
import time

import itertools

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:   prog d D seed time_limit [extra]  < start_graph
 *   stdin:  "n m" then m lines "u v", or "0 0" for none.
 *   stdout: "n m" then m lines "u v": the largest valid graph found.
 * Phase 1: bi-Cayley lift sweep. Groups: finite matrix groups over GF(q) (SL, PSL, PGL)
 *          and random semidirect products Z_m x| Z_k. Base multigraph has p A-fibres and
 *          p B-fibres (p = 1 or 2), darts (i,j,g) join A_{i,x} to B_{j,x*g}.
 * Phase 2: grow-by-two annealing from the best graph found.
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
#define MAXG 1100
#define MAXQ 16
#define MAXQ4 28561
#define SWEEP_SPREAD 12
#define NSPEC 18

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

/* Full all-pairs check by bitsets: number of unordered pairs at distance > D. */
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

/* ------------------------------------------------------------------ groups
 * The current group is GT[x][y] on elements 0..GN-1, identity = 0.
 */
static int GN;
static int GT[MAXG][MAXG];

/* Z_m x|_r Z_k: element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static void build_semidirect(int m, int k, int r) {
    static long rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = rp[b - 1] * r % m;
    GN = m * k;
    for (int x = 0; x < GN; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < GN; y++) {
            int c = y / k, e = y % k;
            GT[x][y] = (int)(((a + rp[b] * c) % m) * k + (b + e) % k);
        }
    }
}

static void random_semidirect(int N) {
    int divs[64], nd = 0;
    for (int m = 1; m <= N && nd < 64; m++)
        if (N % m == 0) divs[nd++] = m;
    for (int tries = 0; tries < 60; tries++) {
        int m = divs[rndint(nd)];
        int k = N / m;
        int r = 1;
        if (m > 1) r = 1 + rndint(m - 1);
        if (m > 1 && gcd(r, m) != 1) continue;
        if (powmod(r, k, m) != 1 % m) continue;
        build_semidirect(m, k, r);
        return;
    }
    build_semidirect(N, 1, 1);
}

/* Finite field GF(q), q = p^k, k <= 3. Elements are ints 0..q-1 (base-p digits). */
static int FQ, FP, FK;
static int FADD[MAXQ][MAXQ], FMUL[MAXQ][MAXQ], FNEG[MAXQ];

static int ipow_int(int b, int e) {
    int r = 1;
    while (e-- > 0) r *= b;
    return r;
}

static int build_field(int q) {
    if (q < 2 || q > MAXQ) return 0;
    int p = 0;
    for (int t = 2; t <= q; t++)
        if (q % t == 0) { p = t; break; }
    int k = 0, r = q;
    while (r % p == 0) { r /= p; k++; }
    if (r != 1 || k < 1 || k > 3) return 0;
    FQ = q;
    FP = p;
    FK = k;
    int f[3] = {0, 0, 0};  /* monic x^k + sum f[i] x^i, irreducible */
    if (k >= 2) {
        int total = ipow_int(p, k), ok = 0;
        for (int code = 0; code < total && !ok; code++) {
            int c = code;
            for (int i = 0; i < k; i++) { f[i] = c % p; c /= p; }
            ok = 1;
            for (int t = 0; t < p && ok; t++) {
                int val = 0, pw = 1;
                for (int i = 0; i < k; i++) {
                    val = (val + f[i] * pw) % p;
                    pw = pw * t % p;
                }
                val = (val + pw) % p;  /* pw is now t^k */
                if (val == 0) ok = 0;
            }
        }
        if (!ok) return 0;
    }
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            int da[3], db[3], s = 0, pw = 1;
            int x = a, y = b;
            for (int i = 0; i < k; i++) {
                da[i] = x % p; x /= p;
                db[i] = y % p; y /= p;
            }
            for (int i = 0; i < k; i++) { s += ((da[i] + db[i]) % p) * pw; pw *= p; }
            FADD[a][b] = s;
            int prod[5] = {0, 0, 0, 0, 0};
            for (int i = 0; i < k; i++)
                for (int j = 0; j < k; j++)
                    prod[i + j] = (prod[i + j] + da[i] * db[j]) % p;
            for (int deg = 2 * k - 2; deg >= k; deg--) {
                int c = prod[deg];
                prod[deg] = 0;
                for (int i = 0; i < k; i++)
                    prod[deg - k + i] = ((prod[deg - k + i] - c * f[i]) % p + p) % p;
            }
            s = 0;
            pw = 1;
            for (int i = 0; i < k; i++) { s += prod[i] * pw; pw *= p; }
            FMUL[a][b] = s;
        }
    for (int a = 0; a < q; a++) {
        int x = a, s = 0, pw = 1;
        for (int i = 0; i < k; i++) {
            s += ((p - x % p) % p) * pw;
            x /= p;
            pw *= p;
        }
        FNEG[a] = s;
    }
    return 1;
}

static int enc4(const int v[4]) { return ((v[0] * FQ + v[1]) * FQ + v[2]) * FQ + v[3]; }

static void dec4(int x, int v[4]) {
    v[3] = x % FQ; x /= FQ;
    v[2] = x % FQ; x /= FQ;
    v[1] = x % FQ; x /= FQ;
    v[0] = x;
}

static int det4(const int v[4]) {
    return FADD[FMUL[v[0]][v[3]]][FNEG[FMUL[v[1]][v[2]]]];
}

/* Canonical code of a matrix up to the equivalence of the group type:
 * type 0 = SL(2,q) (no quotient), 1 = PSL(2,q) (quotient by -1), 2 = PGL(2,q) (scalars). */
static int canon4(int e, int type) {
    int v[4], w[4];
    dec4(e, v);
    if (type == 0) return e;
    if (type == 1) {
        for (int i = 0; i < 4; i++) w[i] = FNEG[v[i]];
        int e2 = enc4(w);
        return e < e2 ? e : e2;
    }
    int best = e;
    for (int l = 1; l < FQ; l++) {
        for (int i = 0; i < 4; i++) w[i] = FMUL[l][v[i]];
        int e2 = enc4(w);
        if (e2 < best) best = e2;
    }
    return best;
}

static int canon_id[MAXQ4];
static int gid[MAXQ4];
static int rep_mat[MAXG][4];

static int build_matrix_group(int q, int type) {
    if (!build_field(q)) return 0;
    int Q4 = q * q * q * q;
    int expect = q * (q * q - 1);
    if (type == 1 && q % 2 == 1) expect /= 2;
    for (int e = 0; e < Q4; e++) canon_id[e] = -1;
    int v[4];
    GN = 1;
    rep_mat[0][0] = 1; rep_mat[0][1] = 0; rep_mat[0][2] = 0; rep_mat[0][3] = 1;
    canon_id[canon4(enc4(rep_mat[0]), type)] = 0;
    for (int e = 0; e < Q4; e++) {
        dec4(e, v);
        int dt = det4(v);
        if (type == 2 ? dt == 0 : dt != 1) continue;
        int c = canon4(e, type);
        if (canon_id[c] < 0) {
            if (GN >= MAXG) return 0;
            canon_id[c] = GN;
            dec4(c, rep_mat[GN]);
            GN++;
        }
    }
    if (GN != expect) return 0;
    for (int e = 0; e < Q4; e++) {
        dec4(e, v);
        int dt = det4(v);
        gid[e] = -1;
        if (type == 2 ? dt == 0 : dt != 1) continue;
        gid[e] = canon_id[canon4(e, type)];
    }
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++) {
            const int *A = rep_mat[x], *B = rep_mat[y];
            int C[4];
            C[0] = FADD[FMUL[A[0]][B[0]]][FMUL[A[1]][B[2]]];
            C[1] = FADD[FMUL[A[0]][B[1]]][FMUL[A[1]][B[3]]];
            C[2] = FADD[FMUL[A[2]][B[0]]][FMUL[A[3]][B[2]]];
            C[3] = FADD[FMUL[A[2]][B[1]]][FMUL[A[3]][B[3]]];
            int g = gid[enc4(C)];
            if (g < 0) return 0;
            GT[x][y] = g;
        }
    return 1;
}

static const int SPEC[NSPEC][2] = {
    {5, 0}, {5, 1}, {5, 2}, {7, 0}, {7, 1}, {7, 2}, {8, 0}, {8, 1}, {8, 2},
    {9, 0}, {9, 1}, {9, 2}, {11, 0}, {11, 1}, {11, 2}, {13, 0}, {13, 1}, {13, 2}
};

static int spec_order(int q, int type) {
    int o = q * (q * q - 1);
    if (type == 1 && q % 2 == 1) o /= 2;
    return o;
}

/* ------------------------------------------------------------------ lifts */

typedef struct { int i, j, g; } Dart;

/* Random d-regular bipartite base multigraph on p + p vertices, connected. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
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

/* Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x.
 * Dart (i,j,g) joins A_{i,x} to B_{j, x*g}; left multiplication is an automorphism. */
static void build_lift(Graph *g, int p, int N, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, (p + dt[t].j) * N + GT[x][dt[t].g]);
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static int dist_buf[MAXN], queue_buf[MAXN];

/* Orbit-reduced check: BFS from one identity vertex per fibre, counting unreached vertices. */
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

/* Hill-climb the voltages of one random base multigraph over the current group. */
static int try_lift(Graph *cand, int p, int N, int steps, double until) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(cand, p, N, dt, nd);
    long bad = orbit_bad(cand, p, N);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(cand, p, N, dt, nd);
        long nb = orbit_bad(cand, p, N);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
    }
    build_lift(cand, p, N, dt, nd);
    return bad == 0;
}

static void lift_range(int p, int bestn, long moore, int *lo, int *hi) {
    long h = moore / (2 * p);
    if (h > MAXG - 1) h = MAXG - 1;
    if (2L * p * h > MAXN) h = MAXN / (2 * p);
    *hi = (int)h;
    *lo = bestn / (2 * p) + 1;
    if (*lo < d) *lo = d;
}

/* Sweep: pick a group whose lift is just above the best size, search voltages, keep valid
 * lifts larger than the best. Non-abelian matrix groups and semidirect groups alternate. */
static void lift_sweep(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    while (now() < until) {
        int p = rndint(10) < 7 ? 1 : 2;
        int lo, hi;
        lift_range(p, best->n, moore, &lo, &hi);
        if (lo > hi) {
            p = 3 - p;
            lift_range(p, best->n, moore, &lo, &hi);
            if (lo > hi) return;
        }
        int N = 0;
        if (rndint(2) == 0) {
            int pick[NSPEC], cnt = 0;
            for (int s = 0; s < NSPEC; s++) {
                int o = spec_order(SPEC[s][0], SPEC[s][1]);
                if (o >= lo && o <= hi) pick[cnt++] = s;
            }
            if (cnt > 0) {
                int s = pick[rndint(cnt)];
                if (build_matrix_group(SPEC[s][0], SPEC[s][1])) N = GN;
            }
        }
        if (N == 0) {
            int spread = SWEEP_SPREAD + best->n / 60;
            int span = hi - lo + 1;
            if (span > spread) span = spread;
            N = lo + rndint(span);
            random_semidirect(N);
        }
        for (int a = 0; a < 4 && now() < until; a++) {
            if (try_lift(&cand, p, N, 6000, until) && cand.n > best->n && is_valid(&cand)) {
                copy_graph(best, &cand);
                break;
            }
        }
    }
}

/* ------------------------------------------------------------------ repair */

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
        fprintf(stderr, "usage: %s d D seed time_limit [extra] < start_graph\n", argv[0]);
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
        lift_sweep(&best, t0 + (t_end - t0) * 0.6);
        if (best.n > 0) grow_search(&best, t_end);
    }
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


def _h3_lines(pts, index, s):
    """Lines of H(3) from Tits' description, with the right-hand sign multiplier s (1 or 2 mod 3)."""
    P = len(pts)

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1]
                + x[2] * y[6] + x[6] * y[2] - 2 * x[3] * y[3]) % 3

    def norm(v):
        c = next(t for t in v if t)
        inv = 1 if c == 1 else 2
        return tuple((t * inv) % 3 for t in v)

    lines = set()
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            y = pts[j]
            if bil(x, y):
                continue

            def pl(a, b):
                return (x[a] * y[b] - x[b] * y[a]) % 3

            conds = [(pl(1, 2), pl(3, 4)), (pl(5, 4), pl(3, 2)), (pl(2, 0), pl(3, 5)),
                     (pl(6, 5), pl(3, 0)), (pl(0, 1), pl(3, 6)), (pl(4, 6), pl(3, 1))]
            if any((a - s * b) % 3 for a, b in conds):
                continue
            L = set()
            for a in range(3):
                for b in range(3):
                    if a == 0 and b == 0:
                        continue
                    v = tuple((a * x[k] + b * y[k]) % 3 for k in range(7))
                    if any(v):
                        L.add(index[norm(v)])
            if len(L) == 4:
                lines.add(tuple(sorted(L)))
    return lines


def _hexagon_h3():
    """Incidence graph of the split Cayley hexagon H(3): 728 vertices, 4-regular, diameter 6.

    Both sign conventions are tried, and the result is accepted only if lib.is_valid confirms
    it. Returns (n, edges) or None.
    """
    pts = []
    for v in itertools.product(range(3), repeat=7):
        if not any(v):
            continue
        if v[next(i for i, c in enumerate(v) if c)] != 1:
            continue
        if (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % 3:
            continue
        pts.append(v)
    P = len(pts)
    if P != 364:
        return None
    index = {v: i for i, v in enumerate(pts)}
    for s in (1, 2):
        lines = _h3_lines(pts, index, s)
        if len(lines) != P:
            continue
        lines = sorted(lines)
        edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
        if lib.is_valid(2 * P, edges, 4, 6):
            return 2 * P, edges
    return None


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

    if d == 4 and D >= 6:
        try:
            hexg = _hexagon_h3()
        except Exception:
            hexg = None
        if hexg is not None and hexg[0] > best[0] and lib.is_valid(hexg[0], hexg[1], d, D):
            best = hexg

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 6)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
