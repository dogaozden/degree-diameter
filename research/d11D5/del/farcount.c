/* farcount: number of ordered vertex pairs at distance > D in an explicit graph (edge list: n, then "u v").
   Bit-parallel BFS, 64 sources at a time.  usage: farcount edges D */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int D = atoi(argv[2]); long n; if (fscanf(f, "%ld", &n) != 1) return 1;
    long cap = 1 << 20, m = 0; long *U = malloc(cap * 8), *W = malloc(cap * 8); long a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 8); W = realloc(W, cap * 8); } U[m] = a; W[m] = b; m++; }
    long *deg = calloc(n + 1, 8); for (long i = 0; i < m; i++) { deg[U[i]]++; deg[W[i]]++; }
    long *st = calloc(n + 1, 8); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    long *adj = malloc(2 * m * 8), *pos = calloc(n, 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    long maxd = 0; for (long i = 0; i < n; i++) if (deg[i] > maxd) maxd = deg[i];
    uint64_t *vis = malloc(n * 8), *fr = malloc(n * 8), *nx = malloc(n * 8); long far = 0;
    for (long s0 = 0; s0 < n; s0 += 64) {
        memset(vis, 0, n * 8); memset(fr, 0, n * 8); int ns = n - s0 < 64 ? n - s0 : 64;
        for (int k = 0; k < ns; k++) { vis[s0 + k] |= 1ULL << k; fr[s0 + k] |= 1ULL << k; }
        for (int lev = 0; lev < D; lev++) {
            memset(nx, 0, n * 8);
            for (long x = 0; x < n; x++) if (fr[x]) for (long i = st[x]; i < st[x + 1]; i++) nx[adj[i]] |= fr[x];
            for (long x = 0; x < n; x++) { nx[x] &= ~vis[x]; vis[x] |= nx[x]; }
            uint64_t *t = fr; fr = nx; nx = t;
        }
        uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        for (long x = 0; x < n; x++) far += __builtin_popcountll(~vis[x] & full);
    }
    printf("n=%ld edges=%ld maxdeg=%ld far_pairs(>%d)=%ld\n", n, m, maxd, D, far);
    return 0;
}
