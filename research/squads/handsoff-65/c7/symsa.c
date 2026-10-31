/* c7 sa.c: simulated annealing over 2-switches of a bipartite 6-regular graph (edge swaps keep degrees and bipartiteness).
 * Cost = number of unordered vertex pairs at distance > 5 (bit-parallel BFS, full recomputation per move).
 * env: INFILE (edge list: n then "u v" lines, 0-based; sides found by BFS), RANDN (random 6-regular bipartite on RANDN
 *      vertices instead), GROW (number of vertex pairs added to INFILE by 5-edge insertion, see below), SEED (1),
 *      ITERS (moves per round, 200000), T0 (2.0), T1 (0.05), ROUNDS (1), SECS (600), OUT (edge list output file).
 * GROW: a new pair (u in A, v in B) is inserted by deleting 5 edges (a_i b_i) with distinct a_i, b_i and adding
 *       u b_i (i=1..5), v a_i (i=1..5), and uv. Degrees stay 6.
 * Prints "SA round r best b cur c iters i secs s" lines; writes OUT when best improves and at the end. */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1024
#define W 16
#define MAXE (3 * MAXN)
typedef uint64_t u64;

static int n, nw, ne;
static int side[MAXN];
static int adj[MAXN][6], deg[MAXN];
static int EA[MAXE], EB[MAXE];
static u64 LA[MAXN][W], LB[MAXN][W];
static u64 (*cur)[W] = LA, (*nxt)[W] = LB;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (adj[a][k] == b) return 1;
    return 0;
}
static void rep(int v, int old, int nw_) {
    for (int k = 0; k < deg[v]; k++) if (adj[v][k] == old) { adj[v][k] = nw_; return; }
    fprintf(stderr, "rep failed\n"); exit(1);
}
/* swap B-endpoints of edges i and j (2-switch); self-inverse */
static int swap_edges(int i, int j) {
    int a1 = EA[i], b1 = EB[i], a2 = EA[j], b2 = EB[j];
    rep(a1, b1, b2); rep(b1, a1, a2); rep(a2, b2, b1); rep(b2, a2, a1);
    EB[i] = b2; EB[j] = b1;
    return 0;
}
static int valid_switch(int i, int j) {
    int a1 = EA[i], b1 = EB[i], a2 = EA[j], b2 = EB[j];
    if (a1 == a2 || b1 == b2) return 0;
    if (has_edge(a1, b2) || has_edge(a2, b1)) return 0;
    return 1;
}
static long cost_full(void) {
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, nw * 8);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 0; k < 5; k++) {
        for (int v = 0; v < n; v++) {
            u64 *d = nxt[v];
            memcpy(d, cur[v], nw * 8);
            for (int t = 0; t < deg[v]; t++) {
                u64 *s = cur[adj[v][t]];
                for (int w = 0; w < nw; w++) d[w] |= s[w];
            }
        }
        u64 (*tmp)[W] = cur; cur = nxt; nxt = tmp;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += __builtin_popcountll(cur[v][w]);
        bad += n - c;
    }
    return bad / 2;
}
static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d\n", n);
    for (int i = 0; i < ne; i++) fprintf(f, "%d %d\n", EA[i], EB[i]);
    fclose(f);
}
static void build_from_edges(int m, int *U, int *V) {
    /* sides by BFS */
    static int col[MAXN]; for (int v = 0; v < n; v++) col[v] = -1;
    static int q[MAXN];
    static int g[MAXN][6]; /* unused */
    (void)g;
    int *dg = calloc(n, sizeof(int));
    for (int i = 0; i < m; i++) { dg[U[i]]++; dg[V[i]]++; }
    /* adjacency for BFS */
    int *st = calloc(n + 1, sizeof(int));
    for (int v = 0; v < n; v++) st[v + 1] = st[v] + dg[v];
    int *fill = calloc(n, sizeof(int)); int *al = malloc(sizeof(int) * 2 * m + 4);
    for (int i = 0; i < m; i++) {
        al[st[U[i]] + fill[U[i]]++] = V[i];
        al[st[V[i]] + fill[V[i]]++] = U[i];
    }
    int h = 0, t = 0;
    for (int s = 0; s < n; s++) if (col[s] < 0) {
        col[s] = 0; q[t++] = s;
        while (h < t) { int x = q[h++]; for (int k = st[x]; k < st[x + 1]; k++) { int y = al[k]; if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; } else if (col[y] == col[x]) { fprintf(stderr, "not bipartite\n"); exit(1); } } }
    }
    for (int v = 0; v < n; v++) side[v] = col[v];
    ne = 0;
    for (int i = 0; i < m; i++) {
        int a = U[i], b = V[i];
        if (side[a] == 1) { int tmp = a; a = b; b = tmp; }
        EA[ne] = a; EB[ne] = b; ne++;
    }
    memset(deg, 0, sizeof deg);
    for (int i = 0; i < ne; i++) { adj[EA[i]][deg[EA[i]]++] = EB[i]; adj[EB[i]][deg[EB[i]]++] = EA[i]; }
    free(dg); free(st); free(fill); free(al);
}
static void simplify_random(void) {
    /* random graph with multi-edges: repair by random valid switches (not used when simple) */
    (void)0;
}

/* orbit-wise switch: base edge o (index o*K+t, t = 0..K-1 whole-graph edges); swap B-endpoints of base edges o1, o2 for all t */
static int K_, NO_;
static int orbit_swap(int o1, int o2) {
    /* returns 1 if applied (all K switches valid), 0 if rejected (state unchanged) */
    int t;
    for (t = 0; t < K_; t++) {
        int i = o1 * K_ + t, j = o2 * K_ + t;
        if (!valid_switch(i, j)) break;
        swap_edges(i, j);
    }
    if (t == K_) return 1;
    for (int s = 0; s < t; s++) swap_edges(o1 * K_ + s, o2 * K_ + s);
    return 0;
}
static void orbit_unswap(int o1, int o2) { for (int s = 0; s < K_; s++) swap_edges(o1 * K_ + s, o2 * K_ + s); }

int main(void) {
    const char *out = getenv("OUT") ? getenv("OUT") : "c7_sym_best.edges";
    K_ = getenv("K") ? atoi(getenv("K")) : 7;
    NO_ = getenv("NO") ? atoi(getenv("NO")) : 49;   /* orbits per side; n = 2*NO*K */
    long iters = getenv("ITERS") ? atol(getenv("ITERS")) : 200000;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 2.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
    int rounds = getenv("ROUNDS") ? atoi(getenv("ROUNDS")) : 1;
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 600;
    rs ^= (uint64_t)(getenv("SEED") ? atol(getenv("SEED")) : 1) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 10; i++) rnd();
    int K = K_, NO = NO_;
    n = 2 * NO * K;
    if (n > MAXN) { fprintf(stderr, "MAXN\n"); return 2; }
    /* random Z_K-invariant graph: rounds of random 1-factors of the orbit graph with random voltages */
    int EO = 6 * NO;
    ne = 0;
    for (int r = 0; r < 6; r++) {
        int *p = malloc(sizeof(int) * NO); for (int i = 0; i < NO; i++) p[i] = i;
        for (int i = NO - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = p[i]; p[i] = p[j]; p[j] = t; }
        for (int qa = 0; qa < NO; qa++) {
            int qb = p[qa];
            int d = rnd() % K;
            /* orbit o = r*NO+qa : edges (qa*K+t, NO*K + qb*K + (d+t)%K) */
            int o = r * NO + qa;
            for (int t = 0; t < K; t++) {
                int idx = o * K + t;
                EA[idx] = qa * K + t;
                EB[idx] = NO * K + qb * K + (d + t) % K;
            }
        }
        free(p);
    }
    ne = EO * K;
    for (int v = 0; v < n; v++) side[v] = v >= NO * K;
    memset(deg, 0, sizeof deg);
    for (int i = 0; i < ne; i++) { adj[EA[i]][deg[EA[i]]++] = EB[i]; adj[EB[i]][deg[EB[i]]++] = EA[i]; }
    /* repair: find duplicate whole edges and orbit-switch them away */
    for (long it = 0; it < 5000000; it++) {
        int bad = -1;
        for (int i = 0; i < ne && bad < 0; i++) { int c = 0; for (int k = 0; k < deg[EA[i]]; k++) if (adj[EA[i]][k] == EB[i]) c++; if (c > 1) bad = i; }
        if (bad < 0) break;
        int o1 = bad / K, o2 = rnd() % EO;
        if (o1 != o2) orbit_swap(o1, o2);
    }
    for (int v = 0; v < n; v++) if (deg[v] != 6) { fprintf(stderr, "degree %d\n", v); return 2; }
    nw = (n + 63) >> 6;
    long cur_c = cost_full(), best = cur_c;
    fprintf(stderr, "start n=%d K=%d NO=%d cost=%ld\n", n, K, NO, cur_c);
    static int bestEA[MAXE], bestEB[MAXE];
    memcpy(bestEA, EA, sizeof(int) * ne); memcpy(bestEB, EB, sizeof(int) * ne);
    double t0 = now();
    long total = 0;
    for (int r = 0; r < rounds && best > 0; r++) {
        long rbest = cur_c;
        for (long it = 0; it < iters; it++) {
            double T = T0 * pow(T1 / T0, (double)it / iters);
            int o1 = rnd() % EO, o2 = rnd() % EO;
            if (o1 == o2) continue;
            if (!orbit_swap(o1, o2)) continue;
            long c = cost_full();
            long d = c - cur_c;
            total++;
            if (d <= 0 || urand() < exp(-d / T)) {
                cur_c = c;
                if (cur_c < rbest) rbest = cur_c;
                if (cur_c < best) {
                    best = cur_c;
                    memcpy(bestEA, EA, sizeof(int) * ne); memcpy(bestEB, EB, sizeof(int) * ne);
                    printf("BEST %ld round %d it %ld secs %.1f\n", best, r, it, now() - t0); fflush(stdout);
                    if (best == 0) break;
                }
            } else {
                orbit_unswap(o1, o2);
            }
            if ((total & 1023) == 0 && now() - t0 > secs) break;
        }
        printf("ROUND %d rbest %ld cur %ld best %ld evals %ld secs %.1f\n", r, rbest, cur_c, best, total, now() - t0); fflush(stdout);
        if (now() - t0 > secs) break;
    }
    memcpy(EA, bestEA, sizeof(int) * ne); memcpy(EB, bestEB, sizeof(int) * ne);
    write_edges(out);
    printf("RESULT best %ld n %d out %s\n", best, n, out);
    return 0;
}
