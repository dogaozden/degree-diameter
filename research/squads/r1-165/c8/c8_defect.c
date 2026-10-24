/* c8_defect: count (source, vertex) pairs at distance > D (or unreached) for a list of sources.
   Bit-parallel BFS, 64 sources per pass. Usage: c8_defect EDGES SOURCES D
   EDGES: first line n, then "u v" lines (undirected). SOURCES: first line k, then k vertex ids. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int argc, char **argv) {
    if (argc < 4) return 2;
    FILE *f = fopen(argv[1], "r"); int D = atoi(argv[3]);
    if (!f) return 2;
    long n; if (fscanf(f, "%ld", &n) != 1) return 2;
    long cap = 1 << 20, m = 0, a, b;
    long *U = malloc(cap * sizeof(long)), *W = malloc(cap * sizeof(long));
    while (fscanf(f, "%ld %ld", &a, &b) == 2) {
        if (m == cap) { cap *= 2; U = realloc(U, cap * sizeof(long)); W = realloc(W, cap * sizeof(long)); }
        U[m] = a; W[m] = b; m++;
    }
    fclose(f);
    long *deg = calloc(n + 1, sizeof(long));
    for (long i = 0; i < m; i++) { deg[U[i]]++; deg[W[i]]++; }
    long *st = calloc(n + 1, sizeof(long));
    for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    long *adj = malloc(2 * m * sizeof(long)), *pos = calloc(n + 1, sizeof(long));
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    FILE *g = fopen(argv[2], "r"); long ns;
    if (!g || fscanf(g, "%ld", &ns) != 1) return 2;
    long *src = malloc(ns * sizeof(long));
    for (long i = 0; i < ns; i++) if (fscanf(g, "%ld", &src[i]) != 1) return 2;
    fclose(g);
    uint64_t *vis = malloc(n * 8), *fr = malloc(n * 8), *nx = malloc(n * 8);
    long defect = 0, maxdeg = 0;
    for (long x = 0; x < n; x++) if (deg[x] > maxdeg) maxdeg = deg[x];
    for (long s0 = 0; s0 < ns; s0 += 64) {
        int k = (ns - s0 < 64) ? (int)(ns - s0) : 64;
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        for (int j = 0; j < k; j++) { long s = src[s0 + j]; vis[s] |= 1ULL << j; fr[s] |= 1ULL << j; }
        for (int lev = 0; lev < D; lev++) {
            for (long x = 0; x < n; x++) {
                uint64_t acc = 0;
                for (long i = st[x]; i < st[x + 1]; i++) acc |= fr[adj[i]];
                nx[x] = acc & ~vis[x];
            }
            for (long x = 0; x < n; x++) vis[x] |= nx[x];
            uint64_t *t = fr; fr = nx; nx = t;
        }
        uint64_t mask = (k == 64) ? ~0ULL : ((1ULL << k) - 1);
        for (long x = 0; x < n; x++) defect += __builtin_popcountll((~vis[x]) & mask);
    }
    printf("defect %ld n %ld m %ld maxdeg %ld sources %ld D %d\n", defect, n, m, maxdeg, ns, D);
    return 0;
}
