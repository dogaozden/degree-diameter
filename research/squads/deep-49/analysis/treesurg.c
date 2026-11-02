/* treesurg: exhaustive "linked" designs for inserting a* (A side), b* (B side) into a vertex-transitive bipartite
 * 4-regular graph X.  Delete 4 disjoint edges e1..e4 such that each e_k (k >= 2) is joined to an earlier e_j by a kept
 * edge (an X-edge from an endpoint of e_j to an endpoint of e_k): then every deleted edge has a detour of length 3 through
 * a kept edge and a new vertex.  e1 = (0, nbr) (4 choices; 0 is an A vertex, vertex-transitivity).  a* ~ the 4 B ends,
 * b* ~ the 4 A ends.  The alternating paths of pathsurg are the special case of linear chains.
 * Usage: treesurg X.edges D [OUT.edges]   (prints improvements and the final best) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int n0, n, D; static int adj0[8192][4], adj[8192][4], deg[8192];
static uint64_t vis[8192], fr[8192], nx[8192]; static int side[8192];
static long far_count(long lim) {
    long far = 0;
    for (int s0 = 0; s0 < n; s0 += 64) {
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        int ns = (n - s0 < 64) ? n - s0 : 64; uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        for (int k = 0; k < ns; k++) { vis[s0 + k] |= 1ULL << k; fr[s0 + k] |= 1ULL << k; }
        for (int lev = 1; lev <= D; lev++) {
            for (int x = 0; x < n; x++) { uint64_t acc = 0; for (int i = 0; i < deg[x]; i++) acc |= fr[adj[x][i]]; nx[x] = acc & ~vis[x]; }
            for (int x = 0; x < n; x++) vis[x] |= nx[x];
            memcpy(fr, nx, n * 8);
        }
        for (int x = 0; x < n; x++) far += __builtin_popcountll(full & ~vis[x]);
        if (far / 2 > lim) return far / 2;
    }
    return far / 2;
}
static void rm(int a, int b) { for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) { adj[a][i] = adj[a][--deg[a]]; return; } }
static void ad(int a, int b) { adj[a][deg[a]++] = b; adj[b][deg[b]++] = a; }
static int E[4][2]; static long best = 1L << 40, cnt = 0; static char *outf;
/* dedupe: hash set of sorted edge-quadruples */
#define HS (1 << 22)
static uint64_t *hs;
static int seen(void) { uint64_t k[4]; for (int i = 0; i < 4; i++) k[i] = (uint64_t)E[i][0] * 8192 + E[i][1];
    for (int i = 0; i < 4; i++) for (int j = i + 1; j < 4; j++) if (k[j] < k[i]) { uint64_t t = k[i]; k[i] = k[j]; k[j] = t; }
    uint64_t h = 1469598103934665603ULL; for (int i = 0; i < 4; i++) { h ^= k[i]; h *= 1099511628211ULL; } h |= 1;
    size_t p = h & (HS - 1); while (hs[p]) { if (hs[p] == h) return 1; p = (p + 1) & (HS - 1); } hs[p] = h; return 0; }
static int used(int v, int m) { for (int i = 0; i < m; i++) if (E[i][0] == v || E[i][1] == v) return 1; return 0; }
static void eval(void) {
    if (seen()) return;
    memcpy(adj, adj0, sizeof(int) * 4 * n0); for (int i = 0; i < n0; i++) deg[i] = 4; deg[n0] = deg[n0 + 1] = 0;
    for (int e = 0; e < 4; e++) { int A = E[e][0], B = E[e][1]; rm(A, B); rm(B, A); ad(n0, B); ad(n0 + 1, A); }
    long fc = far_count(best); cnt++;
    if (fc < best) { best = fc; printf("best %ld edges", best); for (int e = 0; e < 4; e++) printf(" (%d,%d)", E[e][0], E[e][1]); printf("  (%ld designs)\n", cnt); fflush(stdout);
        if (outf) { FILE *o = fopen(outf, "w"); fprintf(o, "%d\n", n); for (int x = 0; x < n; x++) for (int i = 0; i < deg[x]; i++) if (x < adj[x][i]) fprintf(o, "%d %d\n", x, adj[x][i]); fclose(o); } }
}
static void grow(int m) {
    if (m == 4) { eval(); return; }
    for (int j = 0; j < m; j++) for (int t = 0; t < 2; t++) { int x = E[j][t];
        for (int i = 0; i < 4; i++) { int y = adj0[x][i]; if (y == E[j][1 - t] || used(y, m)) continue;     /* kept edge x-y */
            for (int l = 0; l < 4; l++) { int z = adj0[y][l]; if (z == x || used(z, m)) continue;          /* delete y-z */
                if (side[y] == 0) { E[m][0] = y; E[m][1] = z; } else { E[m][0] = z; E[m][1] = y; }
                grow(m + 1); } } }
}
int main(int c, char **v) {
    FILE *f = fopen(v[1], "r"); D = atoi(v[2]); outf = c > 3 ? v[3] : NULL; int a, b; if (fscanf(f, "%d", &n0) != 1) return 2;
    int d0[8192] = {0}; while (fscanf(f, "%d %d", &a, &b) == 2) { adj0[a][d0[a]++] = b; adj0[b][d0[b]++] = a; }
    for (int i = 0; i < n0; i++) side[i] = i < n0 / 2 ? 0 : 1;   /* A = first half (as in the seed files) */
    n = n0 + 2; hs = calloc(HS, 8);
    for (int i = 0; i < 4; i++) { E[0][0] = 0; E[0][1] = adj0[0][i]; grow(1); }
    printf("FINAL %ld designs, best %ld\n", cnt, best); return 0;
}
