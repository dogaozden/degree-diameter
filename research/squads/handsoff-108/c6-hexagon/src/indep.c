/* indep.c (worker c6): independent check of a lift solution. Builds the explicit lift graph from the definition
 * (vertex (v,h) for base vertex v and group element h of Z_m; edges (p,h)-(N+l,h+hv) for each flag, and
 * (p,h)-(N+sig_t(p), h+mv_t(p))), checks it is simple and (q+1+J)-regular and bipartite, then runs a BFS from every
 * base vertex in copy 0 and reports the diameter and the number of far pairs (distance > 8) from copy-0 sources.
 * usage: indep HEXBIN SOLFILE   (the solution file is in hexeval/lift3 format; m is read from it) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: indep HEXBIN SOLFILE\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); int32_t hd[3]; if (!f || fread(hd, 4, 3, f) != 3) return 1;
    int q = hd[0], N = hd[1], Q1 = q + 1, V0 = 2 * N;
    int32_t *pl = malloc(4L * N * Q1); if (fread(pl, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; fclose(f);
    FILE *s = fopen(argv[2], "r"); int qq, J, m, D; long cost; char line[256];
    if (!s || fscanf(s, "%d %d %d %d %ld\n", &qq, &J, &m, &D, &cost) != 5) { fprintf(stderr, "bad solution\n"); return 1; }
    if (!fgets(line, sizeof line, s)) return 1;
    if (qq != q) { fprintf(stderr, "q mismatch\n"); return 1; }
    int *sig = malloc(sizeof(int) * J * N), *mv = malloc(sizeof(int) * J * N), *hv = malloc(sizeof(int) * N * Q1);
    for (int i = 0; i < J * N; i++) if (fscanf(s, "%d", &sig[i]) != 1) return 1;
    for (int i = 0; i < J * N; i++) if (fscanf(s, "%d", &mv[i]) != 1) return 1;
    for (int i = 0; i < N * Q1; i++) if (fscanf(s, "%d", &hv[i]) != 1) return 1;
    fclose(s);
    long V = (long)V0 * m, deg = Q1 + J;
    int *adj = malloc(sizeof(int) * V * deg), *dg = calloc(V, sizeof(int));
    #define ADD(a, b) do { long _a = (a), _b = (b); adj[_a * deg + dg[_a]++] = (int)_b; adj[_b * deg + dg[_b]++] = (int)_a; } while (0)
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) {
        int p = pl[l * Q1 + k], v = hv[l * Q1 + k];
        for (int h = 0; h < m; h++) ADD((long)p * m + h, (long)(N + l) * m + (h + v) % m);
    }
    for (int t = 0; t < J; t++) for (int p = 0; p < N; p++) {
        int l = sig[t * N + p], v = mv[t * N + p];
        for (int h = 0; h < m; h++) ADD((long)p * m + h, (long)(N + l) * m + (h + v) % m);
    }
    int bad = 0, multi = 0;
    for (long x = 0; x < V; x++) { if (dg[x] != deg) bad++;
        for (int i = 0; i < dg[x]; i++) for (int j = i + 1; j < dg[x]; j++) if (adj[x * deg + i] == adj[x * deg + j]) multi++; }
    printf("q=%d N=%d m=%d J=%d vertices=%ld degree_ok=%s parallel_edges=%d\n", q, N, m, J, V, bad ? "NO" : "yes", multi);
    if (bad) return 2;
    int *dist = malloc(sizeof(int) * V), *qu = malloc(sizeof(int) * V);
    int diam = 0; long far_from_copy0 = 0; long far_pairs_total = 0;
    for (int sb = 0; sb < V0; sb++) {
        long src = (long)sb * m;
        for (long x = 0; x < V; x++) dist[x] = -1;
        int hd2 = 0, tl = 0; dist[src] = 0; qu[tl++] = (int)src;
        while (hd2 < tl) { int u = qu[hd2++]; for (int i = 0; i < deg; i++) { int w = adj[(long)u * deg + i]; if (dist[w] < 0) { dist[w] = dist[u] + 1; qu[tl++] = w; } } }
        if (tl != V) { printf("DISCONNECTED from base vertex %d\n", sb); return 3; }
        for (long x = 0; x < V; x++) { if (dist[x] > diam) diam = dist[x]; if (dist[x] > 8) far_from_copy0++; }
    }
    printf("diameter=%d far_pairs_from_copy0_sources(dist>8)=%ld %s\n", diam, far_from_copy0, (diam <= 8 && !multi && !bad) ? "DIAMETER_OK" : "FAIL");
    return diam <= 8 ? 0 : 4;
}
