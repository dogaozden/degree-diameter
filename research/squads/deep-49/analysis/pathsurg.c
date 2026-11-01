/* pathsurg: exhaustive "alternating path" designs for inserting a* (A side) and b* (B side) into a vertex-transitive
 * bipartite 4-regular graph X.  A non-backtracking path v0 v1 ... v_L from v0 = 0 (A side); delete its edges 1, 3, 5, ...
 * (v0v1, v2v3, ...), keep the others, join a* to the B ends and b* to the A ends of the deleted edges.
 * L = 7: 4 deleted edges (mode 4).  L = 5: 3 deleted edges plus the edge a*b* (mode 3).
 * Every deleted edge then has a detour of length 3 (through a kept path edge and a new vertex).
 * Prints the far-pair count (pairs at distance > D) of every design up to the running best, and the best path.
 * Usage: pathsurg X.edges L D [OUT.edges] */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int n0, n, D, L; static int adj0[8192][4], adj[8192][4], deg[8192];
static uint64_t vis[8192], fr[8192], nx[8192];
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
        if (far / 2 > lim) return far / 2;   /* ordered pairs counted twice overall; rough early exit */
    }
    return far / 2;
}
static void rm(int a, int b) { for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) { adj[a][i] = adj[a][--deg[a]]; return; } }
static void ad(int a, int b) { adj[a][deg[a]++] = b; adj[b][deg[b]++] = a; }
int main(int c, char **v) {
    FILE *f = fopen(v[1], "r"); L = atoi(v[2]); D = atoi(v[3]); int a, b; fscanf(f, "%d", &n0);
    int d0[8192] = {0};
    while (fscanf(f, "%d %d", &a, &b) == 2) { adj0[a][d0[a]++] = b; adj0[b][d0[b]++] = a; }
    n = n0 + 2; int as = n0, bs = n0 + 1;
    int P[16]; long best = 1L << 40; int bestP[16]; long cnt = 0, hist[64] = {0};
    int idx[16]; P[0] = 0; int k = 0; idx[0] = -1;
    /* DFS over non-backtracking paths of length L */
    while (k >= 0) {
        idx[k]++; if (idx[k] >= 4) { k--; continue; }
        int nxt = adj0[P[k]][idx[k]]; if (k > 0 && nxt == P[k - 1]) continue;
        int dup = 0; for (int i = 0; i <= k; i++) if (P[i] == nxt) dup = 1; if (dup) continue;
        P[k + 1] = nxt;
        if (k + 1 < L) { k++; idx[k] = -1; continue; }
        /* build */
        memcpy(adj, adj0, sizeof(int) * 4 * n0); for (int i = 0; i < n0; i++) deg[i] = 4; deg[as] = deg[bs] = 0;
        for (int e = 0; e < L; e += 2) { int x = P[e], y = P[e + 1]; rm(x, y); rm(y, x);
            int A = (e % 2 == 0) ? x : y, B = (e % 2 == 0) ? y : x; ad(as, B); ad(bs, A); }
        if (L % 2 == 1 && L == 5) ad(as, bs);
        long fc = far_count(best); cnt++; if (fc < 64 * 4) hist[fc / 4]++;
        if (fc < best) { best = fc; memcpy(bestP, P, sizeof P); printf("best %ld path", best); for (int i = 0; i <= L; i++) printf(" %d", P[i]); printf("  (%ld designs)\n", cnt); fflush(stdout);
            if (c > 4) { FILE *o = fopen(v[4], "w"); fprintf(o, "%d\n", n); for (int x = 0; x < n; x++) for (int i = 0; i < deg[x]; i++) if (x < adj[x][i]) fprintf(o, "%d %d\n", x, adj[x][i]); fclose(o); } }
    }
    printf("FINAL %ld designs, best %ld\n", cnt, best);
    return 0;
}
