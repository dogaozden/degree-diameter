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

static int SA_EA[MAXE], SA_EB[MAXE], SA_ne;
static void rebuild(void) {
    memset(deg, 0, sizeof(int) * MAXN);
    for (int i = 0; i < ne; i++) { adj[EA[i]][deg[EA[i]]++] = EB[i]; adj[EB[i]][deg[EB[i]]++] = EA[i]; }
}
static int edge_exists(int a, int b) { for (int i = 0; i < ne; i++) if (EA[i] == a && EB[i] == b) return 1; return 0; }
/* contraction of pair (u,v) (u,v adjacent): remove all edges at u or v, pair the 5+5 leftover neighbours */
static int contract(int u, int v) {
    int Bn[6], An[6], nb = 0, na = 0;
    for (int i = 0; i < ne; i++) {
        if (EA[i] == u && EB[i] != v) Bn[nb++] = EB[i];
        if (EB[i] == v && EA[i] != u) An[na++] = EA[i];
    }
    if (nb != 5 || na != 5) return 0;
    int k2 = 0;
    for (int i = 0; i < ne; i++) if (EA[i] != u && EB[i] != v) { EA[k2] = EA[i]; EB[k2] = EB[i]; k2++; }
    ne = k2;
    /* pairing: random permutation of Bn, retry while a pair exists */
    for (int att = 0; att < 50; att++) {
        int p[5] = {0,1,2,3,4};
        for (int i = 4; i > 0; i--) { int j = rnd() % (i + 1); int t = p[i]; p[i] = p[j]; p[j] = t; }
        int ok = 1;
        for (int k = 0; k < 5 && ok; k++) if (edge_exists(An[k], Bn[p[k]])) ok = 0;
        if (ok) {
            for (int k = 0; k < 5; k++) { EA[ne] = An[k]; EB[ne] = Bn[p[k]]; ne++; }
            return 1;
        }
    }
    return 0;
}
/* insertion of pair (u,v) (both currently isolated): splits 5 random edges with distinct endpoints */
static int insert_pair(int u, int v) {
    int ch[5], cnt = 0, tries = 0, ea[5], eb[5];
    while (cnt < 5 && tries < 100000) {
        tries++;
        int i = rnd() % ne, ok = 1;
        for (int k = 0; k < cnt; k++) if (ch[k] == i || ea[k] == EA[i] || eb[k] == EB[i]) ok = 0;
        if (ok) { ch[cnt] = i; ea[cnt] = EA[i]; eb[cnt] = EB[i]; cnt++; }
    }
    if (cnt < 5) return 0;
    for (int a = 0; a < 5; a++) for (int b = a + 1; b < 5; b++) if (ch[b] > ch[a]) { int t = ch[a]; ch[a] = ch[b]; ch[b] = t; }
    for (int k = 0; k < 5; k++) { int i = ch[k]; EA[i] = EA[ne - 1]; EB[i] = EB[ne - 1]; ne--; }
    for (int k = 0; k < 5; k++) { EA[ne] = u; EB[ne] = eb[k]; ne++; }
    for (int k = 0; k < 5; k++) { EA[ne] = ea[k]; EB[ne] = v; ne++; }
    EA[ne] = u; EB[ne] = v; ne++;
    return 1;
}
int main(void) {
    const char *in = getenv("INFILE"), *out = getenv("OUT") ? getenv("OUT") : "c7_lns_best.edges";
    int NS = getenv("NS") ? atoi(getenv("NS")) : 40;
    double T = getenv("T") ? atof(getenv("T")) : 0.5;
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 500;
    rs ^= (uint64_t)(getenv("SEED") ? atol(getenv("SEED")) : 1) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 10; i++) rnd();
    FILE *f = fopen(in, "r"); if (!f) return 2;
    int m0; if (fscanf(f, "%d", &n) != 1) return 2;
    static int U[MAXE], V[MAXE]; m0 = 0;
    int a, b; while (fscanf(f, "%d %d", &a, &b) == 2) { U[m0] = a; V[m0] = b; m0++; }
    fclose(f);
    build_from_edges(m0, U, V);
    nw = (n + 63) >> 6;
    long cur_c = cost_full(), best = cur_c;
    fprintf(stderr, "start n=%d ne=%d cost=%ld\n", n, ne, cur_c);
    static int bestEA[MAXE], bestEB[MAXE];
    memcpy(bestEA, EA, sizeof(int) * ne); memcpy(bestEB, EB, sizeof(int) * ne); int bestne = ne;
    static int S1A[MAXE], S1B[MAXE], S2A[MAXE], S2B[MAXE];
    double t0 = now();
    long steps = 0, acc = 0;
    while (now() - t0 < secs && best > 0) {
        steps++;
        /* current state in S1 (saved) */
        memcpy(S1A, EA, sizeof(int) * ne); memcpy(S1B, EB, sizeof(int) * ne); int n1 = ne;
        int i = rnd() % ne; int u = EA[i], v = EB[i];
        if (!contract(u, v)) { memcpy(EA, S1A, sizeof(int) * n1); memcpy(EB, S1B, sizeof(int) * n1); ne = n1; continue; }
        memcpy(S2A, EA, sizeof(int) * ne); memcpy(S2B, EB, sizeof(int) * ne); int n2 = ne;
        /* sample NS insertions around the contracted graph, keep best */
        long bc = 1L << 60; int have = 0;
        static int BSA[MAXE], BSB[MAXE]; int bne = 0;
        for (int s = 0; s < NS; s++) {
            memcpy(EA, S2A, sizeof(int) * n2); memcpy(EB, S2B, sizeof(int) * n2); ne = n2;
            if (!insert_pair(u, v)) continue;
            rebuild();
            long c = cost_full();
            if (!have || c < bc) { bc = c; have = 1; bne = ne; memcpy(BSA, EA, sizeof(int) * ne); memcpy(BSB, EB, sizeof(int) * ne); }
        }
        if (!have) { memcpy(EA, S1A, sizeof(int) * n1); memcpy(EB, S1B, sizeof(int) * n1); ne = n1; rebuild(); continue; }
        long d = bc - cur_c;
        if (d <= 0 || urand() < exp(-d / T)) {
            memcpy(EA, BSA, sizeof(int) * bne); memcpy(EB, BSB, sizeof(int) * bne); ne = bne;
            rebuild();
            cur_c = bc; acc++;
            if (cur_c < best) {
                best = cur_c; memcpy(bestEA, EA, sizeof(int) * ne); memcpy(bestEB, EB, sizeof(int) * ne); bestne = ne;
                printf("BEST %ld step %ld secs %.1f\n", best, steps, now() - t0); fflush(stdout);
            }
        } else {
            memcpy(EA, S1A, sizeof(int) * n1); memcpy(EB, S1B, sizeof(int) * n1); ne = n1; rebuild();
        }
        if (steps % 500 == 0) { printf("STEP %ld cur %ld best %ld acc %ld secs %.1f\n", steps, cur_c, best, acc, now() - t0); fflush(stdout); }
    }
    memcpy(EA, bestEA, sizeof(int) * bestne); memcpy(EB, bestEB, sizeof(int) * bestne); ne = bestne;
    write_edges(out);
    printf("RESULT best %ld n %d steps %ld acc %ld out %s\n", best, n, steps, acc, out);
    return 0;
}
