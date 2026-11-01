/* Independent checker for Z_n lifts of a DEG-regular base (explicit adjacency, no liftd code).
   Usage: check_lift BASE n D VOLTFILE   (VOLTFILE lines "edge volt"; unlisted edges volt 0; base edges indexed in file order)
   Builds the lift as an explicit CSR graph, checks degree, simplicity, bipartiteness, then BFS from (u,0) for every base
   vertex u (Z_n acts transitively on each fibre, so this covers all sources). Prints VALID/INVALID with max distance. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
    if (argc < 5) return 1;
    FILE *f = fopen(argv[1], "r"); int b; if (fscanf(f, "%d", &b) != 1) return 2;
    int E = 0; int eu[2048], ev[2048];
    while (fscanf(f, "%d %d", &eu[E], &ev[E]) == 2) E++;
    fclose(f);
    long n = atol(argv[2]); int D = atoi(argv[3]);
    int volt[2048] = {0};
    FILE *vf = fopen(argv[4], "r"); if (vf) { int e, x; while (fscanf(vf, "%d %d", &e, &x) == 2) volt[e] = (int)(x % n); fclose(vf); }
    long N = (long)b * n; int DEG = 2 * E / b;
    if (DEG * b != 2 * E) { printf("INVALID not regular\n"); return 0; }
    uint32_t *adj = malloc(N * DEG * 4); int *dg = calloc(N, sizeof(int));
    for (int e = 0; e < E; e++) for (long g = 0; g < n; g++) {
        long x = (long)eu[e] * n + g, y = (long)ev[e] * n + (g + volt[e]) % n;
        if (dg[x] >= DEG || dg[y] >= DEG) { printf("INVALID degree overflow\n"); return 0; }
        adj[x * DEG + dg[x]++] = (uint32_t)y; adj[y * DEG + dg[y]++] = (uint32_t)x;
    }
    for (long v = 0; v < N; v++) if (dg[v] != DEG) { printf("INVALID degree at %ld\n", v); return 0; }
    /* simplicity: no repeated neighbour for a vertex (checked on the fly for sources only is enough for BFS validity; do all) */
    for (long v = 0; v < N; v++) for (int i = 0; i < DEG; i++) for (int j = i + 1; j < DEG; j++)
        if (adj[v * DEG + i] == adj[v * DEG + j]) { printf("INVALID multi-edge at %ld\n", v); return 0; }
    uint8_t *dist = malloc(N); uint32_t *q = malloc(N * 4);
    int worst = 0; long unreached_total = 0; int bad = 0;
    for (int u = 0; u < b; u++) {
        memset(dist, 0xff, N); long s = (long)u * n; long h = 0, t = 0; dist[s] = 0; q[t++] = (uint32_t)s;
        while (h < t) { uint32_t x = q[h++]; int dx = dist[x]; if (dx >= D) continue;
            for (int i = 0; i < DEG; i++) { uint32_t y = adj[(long)x * DEG + i]; if (dist[y] == 0xff) { dist[y] = dx + 1; q[t++] = y; } } }
        if (t != N) { unreached_total += N - t; bad = 1; }
        for (long v = 0; v < N; v++) if (dist[v] != 0xff && dist[v] > worst) worst = dist[v];
    }
    /* bipartiteness: colour by base side: edges join side A=[0,b/2) to B; check via parity of lift vertex base index */
    int bip = 1; for (int e = 0; e < E; e++) if (!(eu[e] < b / 2 && ev[e] >= b / 2)) bip = 0;
    if (bad || worst > D) printf("INVALID N=%ld D=%d maxdist_over_sources=%d unreached=%ld\n", N, D, worst, unreached_total);
    else printf("VALID N=%ld d=%d D=%d maxdist=%d bipartite_base=%d\n", N, DEG, D, worst, bip);
    return 0;
}
