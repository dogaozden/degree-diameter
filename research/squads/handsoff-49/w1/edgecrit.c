/* edgecrit: damage of deleting single edges (big-squad-4-8 job).
   Usage: edgecrit EDGES [D=8] [FIRST=0] [COUNT=all]
   For edges FIRST..FIRST+COUNT-1 (file order) prints "i u v far" = number of unordered pairs at distance > D (or
   unreachable) in the graph with that one edge deleted, minus the far pairs of the graph itself (printed first as
   "base far"). Bit-parallel BFS, about n*n*deg/64 word operations per edge (a few ms at n ~ 2,200). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int n, m, *U, *W, *st, *adj, D;
static uint64_t *vis, *fr, *nx;
static long long farcount(int skip) {   /* far ordered pairs with edge 'skip' removed (skip = -1: none) */
    int su = skip >= 0 ? U[skip] : -1, sv = skip >= 0 ? W[skip] : -1; long long far = 0;
    for (int s0 = 0; s0 < n; s0 += 64) {
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        int ns = (n - s0 < 64) ? n - s0 : 64; uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        for (int k = 0; k < ns; k++) { vis[s0 + k] |= 1ULL << k; fr[s0 + k] |= 1ULL << k; }
        for (int lev = 1; lev <= D; lev++) {
            for (int x = 0; x < n; x++) { uint64_t acc = 0;
                for (int i = st[x]; i < st[x + 1]; i++) { int y = adj[i]; if ((x == su && y == sv) || (x == sv && y == su)) continue; acc |= fr[y]; }
                nx[x] = acc & ~vis[x]; }
            for (int x = 0; x < n; x++) vis[x] |= nx[x];
            uint64_t *t = fr; fr = nx; nx = t;
        }
        for (int x = 0; x < n; x++) far += __builtin_popcountll(full & ~vis[x]);
    }
    return far;
}
int main(int c, char **v) {
    FILE *f = fopen(v[1], "r"); D = c > 2 ? atoi(v[2]) : 8; int first = c > 3 ? atoi(v[3]) : 0, count = c > 4 ? atoi(v[4]) : -1;
    if (!f || fscanf(f, "%d", &n) != 1) return 2;
    int cap = 1 << 16, a, b; U = malloc(cap * 4); W = malloc(cap * 4); int *deg = calloc(n, 4);
    while (fscanf(f, "%d %d", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 4); W = realloc(W, cap * 4); } U[m] = a; W[m] = b; m++; deg[a]++; deg[b]++; }
    st = calloc(n + 1, 4); for (int i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    adj = malloc(2 * m * 4); int *pos = calloc(n, 4);
    for (int i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    vis = malloc(n * 8); fr = malloc(n * 8); nx = malloc(n * 8);
    long long base = farcount(-1) / 2; printf("base far %lld\n", base);
    if (count < 0) count = m - first;
    for (int i = first; i < first + count && i < m; i++) { printf("%d %d %d %lld\n", i, U[i], W[i], farcount(i) / 2 - base); fflush(stdout); }
    return 0;
}
