/* insbest: exhaustive best 2-edge insertion into a cubic bipartite graph.
   Insert a pair (a,b): delete x1y1, x2y2 (x in A, y in B, x1!=x2, y1!=y2), add a~y1,y2,b and b~x1,x2,a.
   Scores every choice of two edges with the all-pairs far count and writes the best graph.
   Usage: insbest IN OUT */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MAXN 256
static int n;
static int adj[MAXN][3];
static uint64_t vis[MAXN], fr[MAXN], nx[MAXN];
static long long far_eval(void) {
    long long total = 0;
    for (int s0 = 0; s0 < n; s0 += 64) {
        int ns = n - s0 < 64 ? n - s0 : 64;
        memset(vis, 0, sizeof vis); memset(fr, 0, sizeof fr);
        for (int k = 0; k < ns; k++) { vis[s0 + k] |= 1ULL << k; fr[s0 + k] |= 1ULL << k; }
        for (int lev = 0; lev < 7; lev++) {
            memset(nx, 0, sizeof nx);
            for (int x = 0; x < n; x++) { uint64_t f = fr[x]; if (!f) continue;
                nx[adj[x][0]] |= f; nx[adj[x][1]] |= f; nx[adj[x][2]] |= f; }
            int any = 0;
            for (int y = 0; y < n; y++) { uint64_t z = nx[y] & ~vis[y]; vis[y] |= z; fr[y] = z; any |= (z != 0); }
            if (!any) break;
        }
        for (int y = 0; y < n; y++) total += __builtin_popcountll(vis[y]);
    }
    return ((long long)n * n - total) / 2;
}
int main(int argc, char **argv) {
    if (argc < 3) return 2;
    FILE *f = fopen(argv[1], "r"); int nn; if (fscanf(f, "%d", &nn) != 1) return 2;
    int E[512][2], ne = 0, a, b; while (fscanf(f, "%d %d", &a, &b) == 2) { E[ne][0] = a; E[ne][1] = b; ne++; } fclose(f);
    int nb[MAXN][3], deg[MAXN] = {0};
    for (int i = 0; i < ne; i++) { nb[E[i][0]][deg[E[i][0]]++] = E[i][1]; nb[E[i][1]][deg[E[i][1]]++] = E[i][0]; }
    int col[MAXN]; for (int x = 0; x < nn; x++) col[x] = -1;
    int q[MAXN], h = 0, t = 0; col[0] = 0; q[t++] = 0;
    while (h < t) { int x = q[h++]; for (int k = 0; k < 3; k++) { int y = nb[x][k]; if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; } } }
    /* edges oriented (x in A = colour 0, y in B) */
    int X[512], Y[512], m = 0;
    for (int i = 0; i < ne; i++) { int u = E[i][0], v = E[i][1]; if (col[u] == 0) { X[m] = u; Y[m] = v; } else { X[m] = v; Y[m] = u; } m++; }
    long long best = 1LL << 40; int bi = -1, bj = -1; long cnt = 0;
    for (int i = 0; i < m; i++) for (int j = i + 1; j < m; j++) {
        if (X[i] == X[j] || Y[i] == Y[j]) continue;
        /* build graph: start from nb, apply insertion */
        n = nn + 2; int a_ = nn, b_ = nn + 1;
        for (int x = 0; x < nn; x++) for (int k = 0; k < 3; k++) adj[x][k] = nb[x][k];
        adj[a_][0] = b_; adj[a_][1] = 0; adj[a_][2] = 0; adj[b_][0] = a_; adj[b_][1] = 0; adj[b_][2] = 0;
        /* replace in adjacency: x1 loses y1 gains b; x2 loses y2 gains b; y1 loses x1 gains a; y2 loses x2 gains a */
        int x1 = X[i], y1 = Y[i], x2 = X[j], y2 = Y[j];
        for (int k = 0; k < 3; k++) { if (adj[x1][k] == y1) adj[x1][k] = b_; if (adj[x2][k] == y2) adj[x2][k] = b_; }
        for (int k = 0; k < 3; k++) { if (adj[y1][k] == x1) adj[y1][k] = a_; if (adj[y2][k] == x2) adj[y2][k] = a_; }
        adj[a_][1] = y1; adj[a_][2] = y2; adj[b_][1] = x1; adj[b_][2] = x2;
        /* a has neighbours y1, y2, b ; b has neighbours x1, x2, a */
        adj[a_][0] = b_; adj[b_][0] = a_;
        long long fv = far_eval(); cnt++;
        if (fv < best) { best = fv; bi = i; bj = j; }
    }
    /* write best */
    int x1 = X[bi], y1 = Y[bi], x2 = X[bj], y2 = Y[bj];
    FILE *g = fopen(argv[2], "w"); fprintf(g, "%d\n", nn + 2);
    for (int i = 0; i < m; i++) { if (i == bi || i == bj) continue; fprintf(g, "%d %d\n", X[i], Y[i]); }
    fprintf(g, "%d %d\n%d %d\n%d %d\n%d %d\n%d %d\n", x1, nn + 1, x2, nn + 1, nn, y1, nn, y2, nn, nn + 1);
    fclose(g);
    fprintf(stderr, "insbest: %ld candidates, best far %lld\n", cnt, best);
    printf("%lld\n", best);
    return 0;
}
