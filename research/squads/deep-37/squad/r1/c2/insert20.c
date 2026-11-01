/* insert: exhaustive insertion of a new vertex pair x (side of b's... x adjacent to B-vertices) into a cubic bipartite
   graph on n vertices. mode 2: remove edges e1=(a1,b1), e2=(a2,b2), add x-b1, x-b2, x-y, y-a1, y-a2.
   mode 3: remove e1, e2, e3, add x-b1, x-b2, x-b3, y-a1, y-a2, y-a3. Scores far = #unordered pairs at distance > 7
   (bit-parallel BFS). Prints the histogram of far values and writes the best graph.
   usage: insert20 BASE MODE OUTDIR  (c2 copy of src/insert.c: writes the 20 best insertions as OUTDIR/ins<mode>_<rank>_far<F>.edges) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define MAXN 260
static int n, m, ea[400], eb[400], col[MAXN];
static int adj[MAXN][3], deg[MAXN];
#define TOPK 20
static int topf[TOPK], topr[TOPK][3], ntop = 0;
static void offer(int fc, const int *rem, int k) {
    if (ntop == TOPK && fc >= topf[TOPK-1]) return;
    int p = ntop < TOPK ? ntop++ : TOPK-1;
    while (p > 0 && topf[p-1] > fc) { topf[p] = topf[p-1]; for (int t = 0; t < 3; t++) topr[p][t] = topr[p-1][t]; p--; }
    topf[p] = fc; for (int t = 0; t < 3; t++) topr[p][t] = t < k ? rem[t] : -1;
}
static int far_count(int N) {
    int W = (N + 63) / 64; static uint64_t R[MAXN][4], F[MAXN][4], NF[MAXN][4];
    long far = 0;
    for (int blk = 0; blk < W; blk++) {
        for (int v = 0; v < N; v++) { memset(R[v], 0, 8); R[v][0] = 0; }
        for (int v = 0; v < N; v++) { R[v][0] = (v / 64 == blk) ? (1ULL << (v % 64)) : 0; F[v][0] = R[v][0]; }
        for (int step = 0; step < 7; step++) {
            for (int v = 0; v < N; v++) { uint64_t x = 0; for (int j = 0; j < deg[v]; j++) x |= F[adj[v][j]][0]; NF[v][0] = x & ~R[v][0]; }
            for (int v = 0; v < N; v++) { F[v][0] = NF[v][0]; R[v][0] |= NF[v][0]; }
        }
        int nsrc = (blk == W - 1 && N % 64) ? N % 64 : 64;
        for (int v = 0; v < N; v++) far += nsrc - __builtin_popcountll(R[v][0]);
    }
    return (int)(far / 2);
}
static void build(int *rem, int k) {
    memset(deg, 0, sizeof deg);
    for (int i = 0; i < m; i++) { int skip = 0; for (int t = 0; t < k; t++) if (rem[t] == i) skip = 1; if (skip) continue;
        adj[ea[i]][deg[ea[i]]++] = eb[i]; adj[eb[i]][deg[eb[i]]++] = ea[i]; }
    int x = n, y = n + 1;  /* x on side of a's (adjacent to b's), y on side of b's */
    for (int t = 0; t < k; t++) { int a = ea[rem[t]], b = eb[rem[t]];
        adj[x][deg[x]++] = b; adj[b][deg[b]++] = x; adj[y][deg[y]++] = a; adj[a][deg[a]++] = y; }
    if (k == 2) { adj[x][deg[x]++] = y; adj[y][deg[y]++] = x; }
}
static int isedge(int a, int b) { for (int j = 0; j < deg[a]; j++) if (adj[a][j] == b) return 1; return 0; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int mode = atoi(argv[2]);
    fscanf(f, "%d", &n); int a, b; m = 0;
    int A[400], B[400];
    while (fscanf(f, "%d %d", &a, &b) == 2) { A[m] = a; B[m] = b; m++; } fclose(f);
    /* 2-colour */
    for (int i = 0; i < n; i++) col[i] = -1; col[0] = 0;
    for (int it = 0; it < n; it++) for (int i = 0; i < m; i++) { if (col[A[i]] >= 0 && col[B[i]] < 0) col[B[i]] = 1 - col[A[i]]; if (col[B[i]] >= 0 && col[A[i]] < 0) col[A[i]] = 1 - col[B[i]]; }
    for (int i = 0; i < m; i++) { if (col[A[i]] == 0) { ea[i] = A[i]; eb[i] = B[i]; } else { ea[i] = B[i]; eb[i] = A[i]; } }
    long hist[20000] = {0}; int best = 1 << 30; int bestrem[3];
    int rem[3];
    if (mode == 2) {
        for (int i = 0; i < m; i++) for (int j = i + 1; j < m; j++) {
            if (ea[i] == ea[j] || eb[i] == eb[j]) continue;
            rem[0] = i; rem[1] = j; build(rem, 2);
            int fc = far_count(n + 2); hist[fc < 19999 ? fc : 19999]++;
            if (fc < best) { best = fc; memcpy(bestrem, rem, sizeof rem); }
            offer(fc, rem, 2);
        }
    } else {
        for (int i = 0; i < m; i++) for (int j = i + 1; j < m; j++) for (int k = j + 1; k < m; k++) {
            if (ea[i] == ea[j] || eb[i] == eb[j] || ea[i] == ea[k] || eb[i] == eb[k] || ea[j] == ea[k] || eb[j] == eb[k]) continue;
            rem[0] = i; rem[1] = j; rem[2] = k; build(rem, 3);
            int fc = far_count(n + 2); hist[fc < 19999 ? fc : 19999]++;
            if (fc < best) { best = fc; memcpy(bestrem, rem, sizeof rem); }
            offer(fc, rem, 3);
        }
    }
    printf("best far %d; histogram (lowest values):", best);
    int shown = 0; for (int v = 0; v < 20000 && shown < 8; v++) if (hist[v]) { printf(" %d:%ld", v, hist[v]); shown++; }
    printf("\n");
    for (int r = 0; r < ntop; r++) {
        build(topr[r], mode);
        char fn[512]; snprintf(fn, sizeof fn, "%s/ins%d_%02d_far%d.edges", argv[3], mode, r, topf[r]);
        FILE *o = fopen(fn, "w"); fprintf(o, "%d\n", n + 2);
        for (int v = 0; v < n + 2; v++) for (int j = 0; j < deg[v]; j++) if (adj[v][j] > v) fprintf(o, "%d %d\n", v, adj[v][j]);
        fclose(o);
        printf("rank %d far %d removed %d %d %d\n", r, topf[r], ea[topr[r][0]], eb[topr[r][0]], topr[r][1] >= 0 ? topr[r][1] : -1);
    }
    return 0;
}
