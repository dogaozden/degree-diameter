/* scaffold: hubs on the (16,5) graph G hung on a projective-plane scaffold (job beyond-small, director).
 *
 * For each side s (0: hubs on side A with old neighbours in B; 1: the mirror image):
 *   hubs      h  (side s)   : 16 old neighbours (a covering 4-line hub) + 1 edge to its connector;
 *   connectors c (other side): HPC hubs + the K roots of its line of PG(2, K-1) + 1 cross edge;
 *   roots      R (side s)   : the connectors whose line contains R (<= 17).
 * Cross edges: connector i of structure 0 ~ connector i of structure 1 (they lie on opposite sides).
 * Any two hubs of a structure meet in a root (two lines of a projective plane meet), so they are within 4 without any
 * condition on their old neighbourhoods. What remains (root domination, connector coverage) is checked exactly:
 * cost = number of ordered pairs (new vertex, any vertex) at distance > 5, by bit-parallel BFS from all new vertices
 * (old-old distances do not grow). Local search: swap hubs between connectors / with the pool, permute the cross matching.
 *
 * usage: scaffold EDGES HUBS_A HUBS_B K NCONN SEED STEPS STATE_OUT EDGES_OUT
 *   HUBS_A: hub lines (global ids of old B-vertices), HUBS_B likewise (old A-vertices). Only 16-vertex hubs are used.
 *   NCONN connectors per structure (lines of PG(2,K-1) used round-robin), HPC = 17 - K - 1 hubs per connector. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define MAXN 40000
#define DEG 17
static int n0, n, K, NC, HPC;
static int adj[MAXN][DEG], dg[MAXN];
static int npool[2], pool[2][2000][16];
static int sel[2][4000];            /* sel[s][c*HPC + j] = pool index of the j-th hub of connector c */
static int inuse[2][2000];
static int line_of[4000];          /* line of connector c (same for both structures) */
static int matchp[4000];           /* structure-0 connector c is matched to structure-1 connector matchp[c] */
static int npts, lines[64][8];     /* PG(2,K-1): npts points, npts lines of K points */
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void add_edge(int u, int v) { adj[u][dg[u]++] = v; adj[v][dg[v]++] = u; }

/* projective plane of order q = K-1 (q = 1: triangle; q prime or 4) */
static void make_plane(int q) {
    if (q == 1) { npts = 3; int L[3][2] = {{0,1},{0,2},{1,2}}; for (int i = 0; i < 3; i++) { lines[i][0] = L[i][0]; lines[i][1] = L[i][1]; } return; }
    int add[8][8], mul[8][8];
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) {
        if (q == 4) { add[a][b] = a ^ b; int M[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}}; mul[a][b] = M[a][b]; }
        else { add[a][b] = (a + b) % q; mul[a][b] = a * b % q; } }
    int P[64][3]; npts = 0;
    for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) { P[npts][0] = 1; P[npts][1] = x; P[npts][2] = y; npts++; }
    for (int y = 0; y < q; y++) { P[npts][0] = 0; P[npts][1] = 1; P[npts][2] = y; npts++; }
    P[npts][0] = 0; P[npts][1] = 0; P[npts][2] = 1; npts++;
    for (int l = 0; l < npts; l++) { int c = 0;
        for (int p = 0; p < npts; p++) { int s = 0; for (int k = 0; k < 3; k++) s = add[s][mul[P[l][k]][P[p][k]]]; if (s == 0) lines[l][c++] = p; }
        if (c != K) { fprintf(stderr, "plane error: line %d has %d points\n", l, c); exit(1); } }
}

/* vertex layout of new vertices */
static int hubv(int s, int c, int j) { return n0 + s * (NC * HPC) + c * HPC + j; }
static int connv(int s, int c) { return n0 + 2 * NC * HPC + s * NC + c; }
static int rootv(int s, int r) { return n0 + 2 * NC * HPC + 2 * NC + s * npts + r; }

static int base_dg[MAXN], base_adj[MAXN][DEG];
static void build(void) {
    memcpy(dg, base_dg, sizeof(int) * n0); memcpy(adj, base_adj, sizeof(int) * DEG * n0);
    for (int v = n0; v < n; v++) dg[v] = 0;
    for (int s = 0; s < 2; s++) for (int c = 0; c < NC; c++) {
        for (int j = 0; j < HPC; j++) { int h = hubv(s, c, j), p = sel[s][c * HPC + j];
            for (int k = 0; k < 16; k++) add_edge(h, pool[s][p][k]);
            add_edge(h, connv(s, c)); }
        for (int k = 0; k < K; k++) add_edge(connv(s, c), rootv(s, lines[line_of[c]][k]));
    }
    for (int c = 0; c < NC; c++) add_edge(connv(0, c), connv(1, matchp[c]));
}
static uint64_t vis[MAXN], fr[MAXN], nx[MAXN];
static long cost(long cap, long *per) {
    long far = 0; int ns_tot = n - n0;
    if (per) memset(per, 0, sizeof(long) * ns_tot);
    for (int k0 = 0; k0 < ns_tot; k0 += 64) {
        int ns = ns_tot - k0 < 64 ? ns_tot - k0 : 64;
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        for (int k = 0; k < ns; k++) { vis[n0 + k0 + k] |= 1ULL << k; fr[n0 + k0 + k] |= 1ULL << k; }
        for (int lev = 0; lev < 5; lev++) {
            for (int x = 0; x < n; x++) { uint64_t a = 0; for (int i = 0; i < dg[x]; i++) a |= fr[adj[x][i]]; nx[x] = a & ~vis[x]; }
            for (int x = 0; x < n; x++) vis[x] |= nx[x];
            uint64_t *t = fr; (void)t; memcpy(fr, nx, n * 8);
        }
        uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        for (int x = 0; x < n; x++) { uint64_t m = full & ~vis[x]; if (m) { far += __builtin_popcountll(m);
            if (per) while (m) { int b = __builtin_ctzll(m); m &= m - 1; per[k0 + b]++; } } }
        if (far >= cap) return far;
    }
    return far;
}

static int read_hubs(const char *fn, int s) {
    FILE *f = fopen(fn, "r"); char line[4096]; int c = 0;
    while (fgets(line, sizeof line, f) && c < 2000) { int v[20], m = 0; char *p = line;
        while (m < 20) { int x, k; if (sscanf(p, "%d%n", &x, &k) != 1) break; v[m++] = x; p += k; }
        if (m == 16) { memcpy(pool[s][c], v, sizeof(int) * 16); c++; } }
    fclose(f); return c;
}

int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: scaffold EDGES HUBS_A HUBS_B K NCONN SEED STEPS STATE_OUT EDGES_OUT\n"); return 2; }
    K = atoi(argv[4]); NC = atoi(argv[5]); HPC = DEG - K - 1; rs ^= (unsigned long long)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL;
    long steps = atol(argv[7]);
    make_plane(K - 1);
    FILE *f = fopen(argv[1], "r"); long u, v; if (fscanf(f, "%d", &n0) != 1) return 3;
    while (fscanf(f, "%ld %ld", &u, &v) == 2) { base_adj[u][base_dg[u]++] = v; base_adj[v][base_dg[v]++] = u; }
    fclose(f);
    npool[0] = read_hubs(argv[2], 0); npool[1] = read_hubs(argv[3], 1);
    if (npool[0] < NC * HPC || npool[1] < NC * HPC) { fprintf(stderr, "need %d hubs per side, have %d / %d\n", NC * HPC, npool[0], npool[1]); return 4; }
    n = n0 + 2 * NC * HPC + 2 * NC + 2 * npts;
    if (n > MAXN) return 5;
    /* root degrees: lines used round-robin */
    int rdeg[64] = {0};
    for (int c = 0; c < NC; c++) { line_of[c] = c % npts; for (int k = 0; k < K; k++) rdeg[lines[line_of[c]][k]]++; }
    for (int r = 0; r < npts; r++) if (rdeg[r] > DEG) { fprintf(stderr, "root degree %d > 17\n", rdeg[r]); return 6; }
    for (int s = 0; s < 2; s++) { for (int i = 0; i < NC * HPC; i++) { sel[s][i] = i; inuse[s][i] = 1; } }
    for (int c = 0; c < NC; c++) matchp[c] = c;
    build();
    long *per = malloc(sizeof(long) * (n - n0));
    long cur = cost(1L << 60, per), best = cur; double t0 = now();
    printf("K=%d plane points %d, connectors %d per side, %d hubs per connector, n = %d, start cost %ld\n", K, npts, NC, HPC, n, cur); fflush(stdout);
    int bsel[2][4000], bmatch[4000]; memcpy(bsel, sel, sizeof sel); memcpy(bmatch, matchp, sizeof matchp);
    for (long st = 0; st < steps && best > 0; st++) {
        int s = rnd() & 1, mv = rnd() % 3; int a = -1, b = -1, oa = 0, ob = 0;
        if (mv == 0) { a = rnd() % (NC * HPC); b = rnd() % (NC * HPC); if (a / HPC == b / HPC) continue; int t = sel[s][a]; sel[s][a] = sel[s][b]; sel[s][b] = t; }
        else if (mv == 1) { a = rnd() % (NC * HPC); b = rnd() % npool[s]; if (inuse[s][b]) continue; oa = sel[s][a]; sel[s][a] = b; inuse[s][b] = 1; inuse[s][oa] = 0; }
        else { a = rnd() % NC; b = rnd() % NC; if (a == b) continue; int t = matchp[a]; matchp[a] = matchp[b]; matchp[b] = t; }
        build();
        long c = cost(cur + 1 + (rnd() % 3 == 0 ? 2 : 0), NULL);
        if (c <= cur) { cur = c; if (c < best) { best = c; memcpy(bsel, sel, sizeof sel); memcpy(bmatch, matchp, sizeof matchp);
                printf("step %ld cost %ld (%.0fs)\n", st, best, now() - t0); fflush(stdout); } }
        else { if (mv == 0) { int t = sel[s][a]; sel[s][a] = sel[s][b]; sel[s][b] = t; }
               else if (mv == 1) { inuse[s][sel[s][a]] = 0; sel[s][a] = oa; inuse[s][oa] = 1; }
               else { int t = matchp[a]; matchp[a] = matchp[b]; matchp[b] = t; } }
        (void)ob;
    }
    memcpy(sel, bsel, sizeof sel); memcpy(matchp, bmatch, sizeof matchp); build();
    long fin = cost(1L << 60, per);
    /* report the worst new vertices by type */
    long th = 0, tc = 0, tr = 0;
    for (int s = 0; s < 2; s++) for (int c = 0; c < NC; c++) { for (int j = 0; j < HPC; j++) th += per[hubv(s, c, j) - n0]; tc += per[connv(s, c) - n0]; }
    for (int s = 0; s < 2; s++) for (int r = 0; r < npts; r++) tr += per[rootv(s, r) - n0];
    printf("FINAL cost %ld (hubs %ld, connectors %ld, roots %ld) n = %d\n", fin, th, tc, tr, n);
    FILE *g = fopen(argv[8], "w");
    for (int s = 0; s < 2; s++) { for (int i = 0; i < NC * HPC; i++) fprintf(g, "%d ", sel[s][i]); fprintf(g, "\n"); }
    for (int c = 0; c < NC; c++) fprintf(g, "%d ", matchp[c]); fprintf(g, "\n"); fclose(g);
    g = fopen(argv[9], "w"); fprintf(g, "%d\n", n);
    for (int x = 0; x < n; x++) for (int i = 0; i < dg[x]; i++) if (adj[x][i] > x) fprintf(g, "%d %d\n", x, adj[x][i]);
    fclose(g);
    return 0;
}
