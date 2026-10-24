/* apsp.c: assumption-free diameter of a graph given as an edge list (first line n, then "u v" lines).
   Bit-parallel BFS from every vertex (64 sources per pass). Also reports min/max degree, repeated edges,
   bipartiteness and connectivity. No symmetry is assumed.
   Usage: apsp EDGES [THREADS]      (compile: gcc -O3 -march=native -fopenmp -o apsp apsp.c)
   Cost ~ (n/64) * diameter * 2m word operations: fine up to a few 10^5 vertices. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef _OPENMP
#include <omp.h>
#endif

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: apsp EDGES [THREADS]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    long long n; if (fscanf(f, "%lld", &n) != 1) return 2;
    long long cap = 1 << 20, m = 0; int *U = malloc(sizeof(int) * cap), *V = malloc(sizeof(int) * cap);
    long long a, b;
    while (fscanf(f, "%lld %lld", &a, &b) == 2) {
        if (a < 0 || b < 0 || a >= n || b >= n) { fprintf(stderr, "vertex out of range\n"); return 2; }
        if (m == cap) { cap *= 2; U = realloc(U, sizeof(int) * cap); V = realloc(V, sizeof(int) * cap); }
        U[m] = (int)a; V[m] = (int)b; m++;
    }
    fclose(f);
    long long *off = calloc(n + 1, sizeof(long long)); int *adj = malloc(sizeof(int) * 2 * m);
    long long loops = 0;
    for (long long i = 0; i < m; i++) { if (U[i] == V[i]) loops++; off[U[i] + 1]++; off[V[i] + 1]++; }
    for (long long v = 0; v < n; v++) off[v + 1] += off[v];
    long long *fill = calloc(n, sizeof(long long));
    for (long long i = 0; i < m; i++) { adj[off[U[i]] + fill[U[i]]++] = V[i]; adj[off[V[i]] + fill[V[i]]++] = U[i]; }
    int mind = 1 << 30, maxd = 0; long long rep = 0;
    for (long long v = 0; v < n; v++) {
        int d = (int)(off[v + 1] - off[v]); if (d < mind) mind = d; if (d > maxd) maxd = d;
        /* repeated neighbours: sort the small list */
        int *L = adj + off[v];
        for (int i = 1; i < d; i++) { int x = L[i], j = i - 1; while (j >= 0 && L[j] > x) { L[j + 1] = L[j]; j--; } L[j + 1] = x; }
        for (int i = 1; i < d; i++) if (L[i] == L[i - 1]) rep++;
    }
    /* bipartite */
    int *col = malloc(sizeof(int) * n); for (long long v = 0; v < n; v++) col[v] = -1;
    int *qu = malloc(sizeof(int) * n); int bip = 1; long long comps = 0;
    for (long long s = 0; s < n; s++) if (col[s] < 0) {
        comps++; long long h = 0, t = 0; qu[t++] = (int)s; col[s] = 0;
        while (h < t) { int x = qu[h++]; for (long long j = off[x]; j < off[x + 1]; j++) { int y = adj[j];
            if (col[y] < 0) { col[y] = col[x] ^ 1; qu[t++] = y; } else if (col[y] == col[x]) bip = 0; } }
    }
    printf("n=%lld m=%lld degree min %d max %d repeated %lld loops %lld bipartite %s components %lld\n", n, m, mind, maxd, rep / 2, loops, bip ? "yes" : "no", comps);
    if (comps != 1) { printf("RESULT diameter=inf (disconnected)\n"); return 1; }
    int nth = argc > 2 ? atoi(argv[2]) : 1;
#ifdef _OPENMP
    omp_set_num_threads(nth);
#endif
    long long nb = (n + 63) / 64; int diam = 0;
    #pragma omp parallel
    {
        uint64_t *vis = malloc(8 * n), *fr = malloc(8 * n), *nx = malloc(8 * n);
        int mydiam = 0;
        #pragma omp for schedule(dynamic, 1)
        for (long long bi = 0; bi < nb; bi++) {
            memset(vis, 0, 8 * n); memset(fr, 0, 8 * n);
            long long s0 = bi * 64; int ns = (int)(n - s0 < 64 ? n - s0 : 64);
            for (int i = 0; i < ns; i++) { vis[s0 + i] |= 1ULL << i; fr[s0 + i] |= 1ULL << i; }
            int level = 0;
            for (;;) {
                int any = 0;
                for (long long v = 0; v < n; v++) {
                    uint64_t acc = 0; for (long long j = off[v]; j < off[v + 1]; j++) acc |= fr[adj[j]];
                    acc &= ~vis[v]; nx[v] = acc; if (acc) any = 1;
                }
                if (!any) break;
                level++;
                for (long long v = 0; v < n; v++) vis[v] |= nx[v];
                uint64_t *t = fr; fr = nx; nx = t;
            }
            if (level > mydiam) mydiam = level;
        }
        #pragma omp critical
        { if (mydiam > diam) diam = mydiam; }
        free(vis); free(fr); free(nx);
    }
    printf("RESULT diameter=%d (all-pairs, %lld sources)\n", diam, n);
    return 0;
}
