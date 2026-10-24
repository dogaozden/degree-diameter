/* Independent all-sources BFS check (plain queue BFS from every vertex; no symmetry assumed).
   Input: apsp.c edge-list format.  Prints n, edge count, degree range, 2-colourability, max eccentricity and the
   histogram of distances over all ordered pairs.  usage: bfs_all EDGES */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); long n; if (fscanf(f, "%ld", &n) != 1) return 2;
    long cap = 1 << 20, m = 0, *U = malloc(cap * 8), *V = malloc(cap * 8), a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 8); V = realloc(V, cap * 8); } U[m] = a; V[m] = b; m++; }
    int *deg = calloc(n, sizeof(int)); for (long i = 0; i < m; i++) { deg[U[i]]++; deg[V[i]]++; }
    long *off = calloc(n + 1, 8); for (long i = 0; i < n; i++) off[i + 1] = off[i] + deg[i];
    int *adj = malloc(2 * m * sizeof(int)); int *fill = calloc(n, sizeof(int));
    for (long i = 0; i < m; i++) { adj[off[U[i]] + fill[U[i]]++] = V[i]; adj[off[V[i]] + fill[V[i]]++] = U[i]; }
    int dmin = 1 << 30, dmax = 0; for (long i = 0; i < n; i++) { if (deg[i] < dmin) dmin = deg[i]; if (deg[i] > dmax) dmax = deg[i]; }
    int *dist = malloc(n * sizeof(int)), *q = malloc(n * sizeof(int)); long hist[64] = {0}; int ecc = 0, bip = 1;
    for (long s = 0; s < n; s++) {
        for (long i = 0; i < n; i++) dist[i] = -1;
        int h = 0, t = 0; dist[s] = 0; q[t++] = s;
        while (h < t) { int x = q[h++]; for (long k = off[x]; k < off[x + 1]; k++) { int y = adj[k];
            if (dist[y] < 0) { dist[y] = dist[x] + 1; q[t++] = y; } else if (s == 0 && dist[y] == dist[x]) bip = 0; } }
        if (t != n) { printf("disconnected from %ld\n", s); return 1; }
        for (long i = 0; i < n; i++) { hist[dist[i]]++; if (dist[i] > ecc) ecc = dist[i]; }
    }
    printf("n=%ld edges=%ld degree %d..%d bipartite=%s max_ecc=%d\n", n, m, dmin, dmax, bip ? "yes" : "no", ecc);
    for (int d = 0; d <= ecc; d++) printf("  dist %d: %ld ordered pairs\n", d, hist[d]);
    return 0;
}
