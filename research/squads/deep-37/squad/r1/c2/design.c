/* design.c (deep-37, squad r1, card c2): "designed" insertions into a (3,7) graph on 168 vertices.
   1. load[e] = number of same-side pairs at distance exactly 6 whose unique geodesic uses edge e.
   2. Designs with 4 removed edges e_1..e_4 = (a_j, b_j) (distinct ends): x (new, side 0) joins b_j for j != q,
      y (new, side 1) joins a_j for j != p, and the leftover ends are joined by a_p-b_q (p != q). Edges: 252-4+7 = 255.
      Designs are: (a) alternating edge sets of every 8-cycle, (b) all 4-sets of the LOWLOAD lowest-load edges.
      (c) random 6-edge designs (x takes 3 b's, y takes 3 a's, a perfect matching pairs the 3 leftover a's with the 3
      leftover b's) on the lowload edges.
   Each design is scored by far before repair; the best ones are written to OUTDIR/d<rank>_far<F>.edges.
   usage: design GRAPH168 OUTDIR [LOWLOAD=24] [SAMPLES6=200000] */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define MAXN 192
#define W 3
#define MAXM 300
#define MAXFAR 20000
#define TOP 40

static int n, m, side[MAXN];
static int adj[MAXN][3], aid[MAXN][3];
static int EA[MAXM], EB[MAXM];
static uint64_t mask[W];
static uint64_t R[2][MAXN][W];
static int fu[MAXFAR], fv[MAXFAR], nfar;
static int G168_EA[MAXM], G168_EB[MAXM], G168_m;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndn(int k) { return (int)(rnd() % (uint64_t)k); }

static void build_adj(void) {
    int dc[MAXN]; memset(dc, 0, sizeof dc);
    for (int i = 0; i < m; i++) {
        int a = EA[i], b = EB[i];
        adj[a][dc[a]] = b; aid[a][dc[a]++] = i;
        adj[b][dc[b]] = a; aid[b][dc[b]++] = i;
    }
}
static int eval(void) {
    int cur = 0;
    memset(R[0], 0, sizeof R[0]);
    for (int v = 0; v < n; v++) R[0][v][v >> 6] |= 1ULL << (v & 63);
    for (int it = 0; it < 7; it++) {
        int nx = cur ^ 1;
        for (int v = 0; v < n; v++) {
            int a = adj[v][0], b = adj[v][1], c = adj[v][2];
            for (int w = 0; w < W; w++) R[nx][v][w] = R[cur][v][w] | R[cur][a][w] | R[cur][b][w] | R[cur][c][w];
        }
        cur = nx;
    }
    nfar = 0; int far = 0;
    for (int v = 0; v < n; v++) for (int w = 0; w < W; w++) {
        uint64_t miss = ~R[cur][v][w] & mask[w];
        while (miss) { int u = w * 64 + __builtin_ctzll(miss); miss &= miss - 1;
            if (u > v) { far++; if (nfar < MAXFAR) { fu[nfar] = v; fv[nfar] = u; nfar++; } } }
    }
    return far;
}
static int isadj_base(int a, int b) {
    for (int i = 0; i < G168_m; i++) if ((G168_EA[i] == a && G168_EB[i] == b)) return 1;
    return 0;
}

/* design: removed edge indices rem[0..3] of the 168 graph; q = leftover b index, p = leftover a index.
   Returns far (or -1 if invalid). Writes the 255-edge list to EA/EB and rebuilds adjacency. */
static int make_design4(const int *rem, int p, int q) {
    int a[4], b[4];
    for (int j = 0; j < 4; j++) { a[j] = G168_EA[rem[j]]; b[j] = G168_EB[rem[j]]; }
    for (int j = 0; j < 4; j++) for (int k = j + 1; k < 4; k++) if (a[j] == a[k] || b[j] == b[k]) return -1;
    if (p == q) return -1;
    /* a_p - b_q must be a new edge: not an edge of the 168 graph (edges between removed endpoints count too) */
    if (isadj_base(a[p], b[q])) return -1;
    m = 0;
    for (int i = 0; i < G168_m; i++) {
        int skip = 0; for (int j = 0; j < 4; j++) if (rem[j] == i) skip = 1;
        if (!skip) { EA[m] = G168_EA[i]; EB[m] = G168_EB[i]; m++; }
    }
    n = 170;
    int x = 168, y = 169;
    for (int j = 0; j < 4; j++) if (j != q) { EA[m] = x; EB[m] = b[j]; m++; }
    for (int j = 0; j < 4; j++) if (j != p) { EA[m] = a[j]; EB[m] = y; m++; }
    EA[m] = a[p]; EB[m] = b[q]; m++;
    build_adj();
    return eval();
}

/* top list */
static int topf[TOP]; static int topE[TOP][MAXM * 2]; static int ntop = 0;
static long nevals = 0;
static void offer(int far) {
    if (ntop == TOP && far >= topf[TOP - 1]) return;
    int p = ntop < TOP ? ntop++ : TOP - 1;
    while (p > 0 && topf[p - 1] > far) { topf[p] = topf[p - 1]; memcpy(topE[p], topE[p - 1], sizeof topE[p]); p--; }
    topf[p] = far;
    for (int i = 0; i < m; i++) { topE[p][2 * i] = EA[i]; topE[p][2 * i + 1] = EB[i]; }
}
static int best_far = 1 << 30;
static void consider(int rem0, int rem1, int rem2, int rem3, int p, int q) {
    int rem[4] = {rem0, rem1, rem2, rem3};
    int f = make_design4(rem, p, q);
    nevals++;
    if (f < 0) return;
    if (f < best_far) { best_far = f; }
    offer(f);
}

static int cyc[16], used[MAXN];
static int cycles8 = 0, cycles12 = 0;
static int *cycE8 = NULL, *cycE12 = NULL; static int n8 = 0, cap8 = 0, n12 = 0, cap12 = 0;
static void dfs(int depth, int target, int s) {
    if (depth == target) {
        int last = cyc[depth - 1];
        int closes = 0; for (int k = 0; k < 3; k++) if (adj[last][k] == s) closes = 1;
        if (closes && cyc[1] < cyc[depth - 1]) {       /* each cycle once: min vertex s, orientation fixed */
            int E[12];
            for (int i = 0; i < target; i++) {
                int u = cyc[i], w = cyc[(i + 1) % target]; E[i] = -1;
                for (int k = 0; k < 3; k++) if (adj[u][k] == w) E[i] = aid[u][k];
            }
            if (target == 8) {
                if (n8 == cap8) { cap8 = cap8 ? 2 * cap8 : 1024; cycE8 = realloc(cycE8, cap8 * 8 * sizeof(int)); }
                memcpy(cycE8 + n8 * 8, E, 8 * sizeof(int)); n8++; cycles8++;
            } else {
                if (n12 == cap12) { cap12 = cap12 ? 2 * cap12 : 4096; cycE12 = realloc(cycE12, cap12 * 12 * sizeof(int)); }
                memcpy(cycE12 + n12 * 12, E, 12 * sizeof(int)); n12++; cycles12++;
            }
        }
        return;
    }
    int v = cyc[depth - 1];
    for (int k = 0; k < 3; k++) {
        int w = adj[v][k];
        if (w <= s || used[w]) continue;
        cyc[depth] = w; used[w] = 1;
        dfs(depth + 1, target, s);
        used[w] = 0;
    }
}

/* per-edge load on the base graph */
static int load[MAXM];
static void compute_load(void) {
    /* adjacency of the 168 graph with edge ids */
    int bn = 168;
    static int dist[MAXN], cnt[MAXN], q[MAXN], pe[MAXN], pv[MAXN];
    for (int s = 0; s < bn; s++) {
        for (int v = 0; v < bn; v++) { dist[v] = -1; cnt[v] = 0; }
        int h = 0, t = 0; q[t++] = s; dist[s] = 0; cnt[s] = 1; pe[s] = -1; pv[s] = -1;
        while (h < t) {
            int x = q[h++]; if (dist[x] >= 6) continue;
            for (int k = 0; k < 3; k++) { int y = adj[x][k];
                if (dist[y] < 0) { dist[y] = dist[x] + 1; cnt[y] = cnt[x]; pv[y] = x; pe[y] = aid[x][k]; q[t++] = y; }
                else if (dist[y] == dist[x] + 1) cnt[y] += cnt[x]; }
        }
        for (int v = 0; v < bn; v++) {
            if (dist[v] != 6 || side[v] != side[s] || v <= s || cnt[v] != 1) continue;
            /* unique geodesic: walk back and charge its edges */
            int x = v; while (x != s) { load[pe[x]]++; x = pv[x]; }
        }
    }
}

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: design GRAPH168 OUTDIR [LOWLOAD SAMPLES6]\n"); return 2; }
    int LOW = argc > 3 ? atoi(argv[3]) : 24;
    long SAMPLES6 = argc > 4 ? atol(argv[4]) : 200000;
    double t0 = now();
    FILE *f = fopen(argv[1], "r"); int n0; if (fscanf(f, "%d", &n0) != 1) return 2;
    int A[MAXM], B[MAXM], m0 = 0, a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) { A[m0] = a; B[m0] = b; m0++; }
    fclose(f);
    if (n0 != 168) { fprintf(stderr, "need a 168-vertex graph\n"); return 2; }
    int col[MAXN]; for (int i = 0; i < n0; i++) col[i] = -1; col[0] = 0;
    for (int it = 0; it < n0; it++) for (int i = 0; i < m0; i++) {
        if (col[A[i]] >= 0 && col[B[i]] < 0) col[B[i]] = 1 - col[A[i]];
        if (col[B[i]] >= 0 && col[A[i]] < 0) col[A[i]] = 1 - col[B[i]];
    }
    for (int v = 0; v < n0; v++) side[v] = col[v];
    G168_m = m0;
    for (int i = 0; i < m0; i++) {
        if (side[A[i]] == 0) { G168_EA[i] = A[i]; G168_EB[i] = B[i]; } else { G168_EA[i] = B[i]; G168_EB[i] = A[i]; }
    }
    n = 170; m = m0;
    for (int i = 0; i < m0; i++) { EA[i] = G168_EA[i]; EB[i] = G168_EB[i]; }
    side[168] = 0; side[169] = 1;
    for (int v = 0; v < n; v++) mask[v >> 6] |= 1ULL << (v & 63);
    /* adjacency of the base graph (for cycles and loads): reuse the 168 graph with m0 edges */
    m = m0; n = 168; build_adj();
    for (int v = 0; v < 168; v++) mask[v >> 6] &= ~0ULL;
    compute_load();
    /* load histogram */
    int hist[64] = {0};
    for (int i = 0; i < m0; i++) { int l = load[i] < 63 ? load[i] : 63; hist[l]++; }
    printf("load histogram (unique-geodesic same-side distance-6 pairs per edge):");
    for (int l = 0; l < 64; l++) if (hist[l]) printf(" %d:%d", l, hist[l]);
    printf("\n");
    /* lowest-load edges */
    int ord[MAXM]; for (int i = 0; i < m0; i++) ord[i] = i;
    for (int i = 0; i < m0; i++) for (int j = i + 1; j < m0; j++) if (load[ord[j]] < load[ord[i]]) { int t2 = ord[i]; ord[i] = ord[j]; ord[j] = t2; }
    int LOWN = LOW < m0 ? LOW : m0;
    printf("lowest loads:"); for (int i = 0; i < LOWN && i < 40; i++) printf(" %d", load[ord[i]]); printf("\n");

    /* (a) alternating edge sets of the 8-cycles (exhaustive over p,q) */
    n = 168; m = m0; build_adj();
    for (int s = 0; s < 168; s++) { memset(used, 0, sizeof used); used[s] = 1; cyc[0] = s; dfs(1, 8, s); }
    for (int c = 0; c < n8; c++) for (int par = 0; par < 2; par++) {
        int rem[4], na = 0;
        for (int i = par; i < 8; i += 2) rem[na++] = cycE8[c * 8 + i];
        for (int p = 0; p < 4; p++) for (int q = 0; q < 4; q++) if (p != q) consider(rem[0], rem[1], rem[2], rem[3], p, q);
    }
    printf("8-cycles: %d (designs scored: %ld, best %d, t=%.1f)\n", cycles8, nevals, best_far, now() - t0);
    fflush(stdout);
    /* (b) 4-subsets of the lowest-load edges */
    long before = nevals;
    for (int i0 = 0; i0 < LOWN; i0++) for (int i1 = i0 + 1; i1 < LOWN; i1++) for (int i2 = i1 + 1; i2 < LOWN; i2++) for (int i3 = i2 + 1; i3 < LOWN; i3++) {
        int rem[4] = {ord[i0], ord[i1], ord[i2], ord[i3]};
        for (int p = 0; p < 4; p++) for (int q = 0; q < 4; q++) if (p != q) consider(rem[0], rem[1], rem[2], rem[3], p, q);
    }
    printf("4-subsets of %d lowest-load edges: %ld designs scored, best %d, t=%.1f\n", LOWN, nevals - before, best_far, now() - t0);
    fflush(stdout);
    /* (c) random 12-cycle alternating 6-sets, with x (3 b's), y (3 a's) and a matching of leftovers */
    n = 168; m = m0; build_adj();
    for (int s = 0; s < 168; s++) { memset(used, 0, sizeof used); used[s] = 1; cyc[0] = s; dfs(1, 12, s); }
    printf("12-cycles: %d\n", cycles12); fflush(stdout);
    long nd = 0;
    for (long smp = 0; smp < SAMPLES6 && n12 > 0; smp++) {
        int c = rndn(n12);
        int *cc = cycE12 + c * 12;
        int par = rndn(2);
        int rem[6], na = 0;
        for (int i = par; i < 12; i += 2) rem[na++] = cc[i];
        int ea6[6], eb6[6];
        for (int j = 0; j < 6; j++) { ea6[j] = G168_EA[rem[j]]; eb6[j] = G168_EB[rem[j]]; }
        /* choose 3 b indices for x, 3 a indices for y, pair leftovers by a random permutation */
        int bx[6] = {0,1,2,3,4,5}, ay[6] = {0,1,2,3,4,5};
        for (int i = 5; i > 0; i--) { int j = rndn(i + 1); int t2 = bx[i]; bx[i] = bx[j]; bx[j] = t2; }
        for (int i = 5; i > 0; i--) { int j = rndn(i + 1); int t2 = ay[i]; ay[i] = ay[j]; ay[j] = t2; }
        int lb[3], la[3], nb = 0, na2 = 0;
        int isx[6] = {0}, isy[6] = {0};
        for (int j = 0; j < 3; j++) isx[bx[j]] = 1, isy[ay[j]] = 1;
        for (int j = 0; j < 6; j++) { if (!isx[j]) lb[nb++] = j; if (!isy[j]) la[na2++] = j; }
        /* leftover b's: index lb[], leftover a's: la[]; random matching */
        int perm[3] = {0,1,2};
        for (int i = 2; i > 0; i--) { int j = rndn(i + 1); int t2 = perm[i]; perm[i] = perm[j]; perm[j] = t2; }
        /* build edge list directly */
        m = 0;
        for (int i = 0; i < m0; i++) { int skip = 0; for (int j = 0; j < 6; j++) if (rem[j] == i) skip = 1; if (!skip) { EA[m] = G168_EA[i]; EB[m] = G168_EB[i]; m++; } }
        int ok = 1;
        for (int j = 0; j < 3; j++) { EA[m] = 168; EB[m] = eb6[bx[j]]; m++; }
        for (int j = 0; j < 3; j++) { EA[m] = ea6[ay[j]]; EB[m] = 169; m++; }
        for (int j = 0; j < 3; j++) {
            int A_ = ea6[la[j]], B_ = eb6[lb[perm[j]]];
            if (la[j] == lb[perm[j]]) { ok = 0; break; }   /* same removed edge: no-op */
            if (isadj_base(A_, B_)) { ok = 0; break; }
            EA[m] = A_; EB[m] = B_; m++;
        }
        if (!ok) continue;
        n = 170; build_adj();
        int f = eval();
        nd++; nevals++;
        if (f < best_far) best_far = f;
        offer(f);
    }
    printf("random 12-cycle designs: %ld scored, best %d, t=%.1f\n", nd, best_far, now() - t0);
    /* write the top designs */
    for (int r = 0; r < ntop && r < 30; r++) {
        char fn[512]; snprintf(fn, sizeof fn, "%s/d%02d_far%d.edges", argv[2], r, topf[r]);
        FILE *o = fopen(fn, "w"); fprintf(o, "170\n");
        for (int i = 0; i < 255; i++) fprintf(o, "%d %d\n", topE[r][2 * i], topE[r][2 * i + 1]);
        fclose(o);
    }
    printf("top designs (far before repair):");
    for (int r = 0; r < ntop && r < 30; r++) printf(" %d", topf[r]);
    printf("\nDONE t=%.1f designs=%ld\n", now() - t0, nevals);
    return 0;
}
