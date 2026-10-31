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

/* scan2.c: exhaustive scan of all valid 2-switches (i<j) of the input graph; prints the minimum cost and histogram
 * of costs below the base cost; writes the best switched graph to OUT. env INFILE, OUT, SECS (time limit). */
int main(void) {
    const char *in = getenv("INFILE"), *out = getenv("OUT") ? getenv("OUT") : "c7_scan_best.edges";
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 500;
    FILE *f = fopen(in, "r"); if (!f) return 2;
    int m0; if (fscanf(f, "%d", &n) != 1) return 2;
    static int U[MAXE], V[MAXE]; m0 = 0;
    int a, b; while (fscanf(f, "%d %d", &a, &b) == 2) { U[m0] = a; V[m0] = b; m0++; }
    fclose(f);
    build_from_edges(m0, U, V);
    nw = (n + 63) >> 6;
    long base = cost_full();
    long DTH = getenv("DTH") ? atol(getenv("DTH")) : 10;
    FILE *nf_ = fopen(getenv("NEARFILE") ? getenv("NEARFILE") : "near.txt", "w");
    printf("base n=%d cost=%ld ne=%d\n", n, base, ne); fflush(stdout);
    long bestc = base; int bi = -1, bj = -1; long cnt = 0, valid = 0, lt = 0;
    long hist[16] = {0};
    double t0 = now();
    long ub = 0;
    for (int i = 0; i < ne; i++) {
        for (int j = i + 1; j < ne; j++) {
            cnt++;
            if (!valid_switch(i, j)) continue;
            valid++;
            swap_edges(i, j);
            long c = cost_full();
            swap_edges(i, j);
            long d = c - base;
            if (d < 0) lt++;
            if (d <= DTH) fprintf(nf_, "%d %d %ld\n", i, j, d);
            int hb = d < 0 ? 0 : (d < 20 ? 1 : (d < 40 ? 2 : (d < 60 ? 3 : (d < 100 ? 4 : 5))));
            hist[hb]++;
            if (c < bestc) { bestc = c; bi = i; bj = j; printf("IMPROVE %ld i %d j %d\n", c, i, j); fflush(stdout); }
        }
        if (now() - t0 > secs) { printf("TIMEOUT at i=%d\n", i); break; }
        if (i % 200 == 0) { printf("progress i=%d valid=%ld secs=%.1f best=%ld\n", i, valid, now() - t0, bestc); fflush(stdout); }
    }
    printf("HIST neg %ld d<20 %ld d<40 %ld d<60 %ld d<100 %ld rest %ld\n", hist[0], hist[1], hist[2], hist[3], hist[4], hist[5]);
    fclose(nf_);
    printf("RESULT base %ld bestc %ld valid %ld pairs %ld secs %.1f\n", base, bestc, valid, cnt, now() - t0);
    if (bi >= 0) { swap_edges(bi, bj); FILE *o = fopen(out, "w"); fprintf(o, "%d\n", n); for (int q = 0; q < ne; q++) fprintf(o, "%d %d\n", EA[q], EB[q]); fclose(o); }
    return 0;
}
