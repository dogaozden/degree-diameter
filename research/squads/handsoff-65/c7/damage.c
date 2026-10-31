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

static void rebuild2(void) {
    memset(deg, 0, sizeof(int) * MAXN);
    for (int i = 0; i < ne; i++) { adj[EA[i]][deg[EA[i]]++] = EB[i]; adj[EB[i]][deg[EB[i]]++] = EA[i]; }
}
/* damage.c: per-edge deletion damage on the 684 graph, then damage-guided insertion of one vertex pair */
int main(void) {
    const char *in = getenv("INFILE");
    long samples = getenv("SAMPLES") ? atol(getenv("SAMPLES")) : 400;
    int POOL = getenv("POOL") ? atoi(getenv("POOL")) : 80;
    const char *out = getenv("OUT") ? getenv("OUT") : "c7_dmg_best.edges";
    rs ^= (uint64_t)(getenv("SEED") ? atol(getenv("SEED")) : 1) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 10; i++) rnd();
    FILE *f = fopen(in, "r"); if (!f) return 2;
    int m0; if (fscanf(f, "%d", &n) != 1) return 2;
    static int U[MAXE], V[MAXE]; m0 = 0;
    int a, b; while (fscanf(f, "%d %d", &a, &b) == 2) { U[m0] = a; V[m0] = b; m0++; }
    fclose(f);
    build_from_edges(m0, U, V);
    nw = (n + 63) >> 6;
    long base = cost_full();
    fprintf(stderr, "base n=%d cost=%ld ne=%d\n", n, base, ne);
    static int D[MAXE]; static int ord[MAXE];
    static int EA0[MAXE], EB0[MAXE]; int ne0 = ne;
    memcpy(EA0, EA, sizeof(int) * ne); memcpy(EB0, EB, sizeof(int) * ne);
    int hist[4096] = {0};
    for (int i = 0; i < ne0; i++) {
        /* delete edge i (move last into slot i) */
        memcpy(EA, EA0, sizeof(int) * ne0); memcpy(EB, EB0, sizeof(int) * ne0);
        EA[i] = EA0[ne0 - 1]; EB[i] = EB0[ne0 - 1]; ne = ne0 - 1;
        rebuild2();
        long c = cost_full();
        D[i] = (int)(c - base); ord[i] = i;
        if (D[i] >= 0 && D[i] < 4096) hist[D[i]]++;
    }
    /* histogram of damages */
    printf("DAMAGE min/hist:");
    for (int d = 0; d < 4096; d++) if (hist[d]) printf(" %d:%d", d, hist[d]);
    printf("\n");
    /* sort indices by damage (simple selection of pool) */
    for (int i = 0; i < ne0; i++) for (int j = i + 1; j < ne0; j++) if (D[ord[j]] < D[ord[i]]) { int t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
    /* insertion sampling from the POOL least-damaging edges (distinct endpoints), keep best */
    memcpy(EA, EA0, sizeof(int) * ne0); memcpy(EB, EB0, sizeof(int) * ne0); ne = ne0;
    long bestc = 1L << 60; static int BA[MAXE], BB[MAXE]; int bne = 0;
    int u = n, v = n + 1; int nn = n + 2;
    long hist2[64] = {0};
    for (long s = 0; s < samples; s++) {
        int ch[5], cnt = 0, tries = 0;
        while (cnt < 5 && tries < 10000) {
            tries++;
            int i = ord[rnd() % POOL], ok = 1;
            for (int k = 0; k < cnt; k++) if (ch[k] == i || EA0[ch[k]] == EA0[i] || EB0[ch[k]] == EB0[i]) ok = 0;
            if (ok) ch[cnt++] = i;
        }
        if (cnt < 5) continue;
        /* build the 686 graph */
        int ne1 = 0;
        static int CA[MAXE], CB[MAXE];
        for (int i = 0; i < ne0; i++) { int skip = 0; for (int k = 0; k < 5; k++) if (ch[k] == i) skip = 1; if (!skip) { CA[ne1] = EA0[i]; CB[ne1] = EB0[i]; ne1++; } }
        for (int k = 0; k < 5; k++) { CA[ne1] = u; CB[ne1] = EB0[ch[k]]; ne1++; }
        for (int k = 0; k < 5; k++) { CA[ne1] = EA0[ch[k]]; CB[ne1] = v; ne1++; }
        CA[ne1] = u; CB[ne1] = v; ne1++;
        n = nn; ne = ne1;
        memcpy(EA, CA, sizeof(int) * ne1); memcpy(EB, CB, sizeof(int) * ne1);
        rebuild2();
        nw = (n + 63) >> 6;
        long c = cost_full();
        if (c < bestc) { bestc = c; bne = ne1; memcpy(BA, CA, sizeof(int) * ne1); memcpy(BB, CB, sizeof(int) * ne1); printf("BESTINS %ld sample %ld\n", c, s); fflush(stdout); }
        if (c < 64) hist2[c]++;
        n = nn - 2; ne = ne0;
        nn = n + 2; /* keep nn consistent */
        nn = n + 2;
        nw = (n + 63) >> 6;
    }
    FILE *o = fopen(out, "w"); fprintf(o, "%d\n", nn - 0 > 0 ? (int)(ne0 > 0 ? 686 : 686) : 686);
    fclose(o);
    /* write best graph with n = 686 */
    o = fopen(out, "w"); fprintf(o, "686\n"); for (int i = 0; i < bne; i++) fprintf(o, "%d %d\n", BA[i], BB[i]); fclose(o);
    printf("RESULT bestins %ld out %s\n", bestc, out);
    return 0;
}
